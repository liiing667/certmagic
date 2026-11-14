// Copyright 2015 Matthew Holt
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package certmagic

import (
	"context"
	"crypto/tls"
	"crypto/x509"
	"errors"
	"fmt"
	"net"
	"runtime"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

func TestGetCertificate(t *testing.T) {
	c := &Cache{
		cache:      make(map[string]Certificate),
		cacheIndex: make(map[string][]string),
		logger:     defaultTestLogger,
	}
	cfg := &Config{Logger: defaultTestLogger, certCache: c}

	// create a test connection for conn.LocalAddr()
	l, _ := net.Listen("tcp", "127.0.0.1:0")
	defer l.Close()
	conn, _ := net.Dial("tcp", l.Addr().String())
	if conn == nil {
		t.Errorf("failed to create a test connection")
	}
	defer conn.Close()

	hello := &tls.ClientHelloInfo{ServerName: "example.com", Conn: conn}
	helloSub := &tls.ClientHelloInfo{ServerName: "sub.example.com", Conn: conn}
	helloNoSNI := &tls.ClientHelloInfo{Conn: conn}
	helloNoMatch := &tls.ClientHelloInfo{ServerName: "nomatch", Conn: conn}

	// When cache is empty
	if cert, err := cfg.GetCertificate(hello); err == nil {
		t.Errorf("GetCertificate should return error when cache is empty, got: %v", cert)
	}
	if cert, err := cfg.GetCertificate(helloNoSNI); err == nil {
		t.Errorf("GetCertificate should return error when cache is empty even if server name is blank, got: %v", cert)
	}

	// When cache has one certificate in it
	firstCert := Certificate{Names: []string{"example.com"}, Certificate: tls.Certificate{Leaf: &x509.Certificate{DNSNames: []string{"example.com"}}}}
	c.cacheCertificate(firstCert)
	if cert, err := cfg.GetCertificate(hello); err != nil {
		t.Errorf("Got an error but shouldn't have, when cert exists in cache: %v", err)
	} else if cert.Leaf.DNSNames[0] != "example.com" {
		t.Errorf("Got wrong certificate with exact match; expected 'example.com', got: %v", cert)
	}
	if _, err := cfg.GetCertificate(helloNoSNI); err == nil {
		t.Errorf("Did not get an error with no SNI and no DefaultServerName, but should have: %v", err)
	}

	// When retrieving wildcard certificate
	wildcardCert := Certificate{
		Names:       []string{"*.example.com"},
		Certificate: tls.Certificate{Leaf: &x509.Certificate{DNSNames: []string{"*.example.com"}}},
		hash:        "(don't overwrite the first one)",
	}
	c.cacheCertificate(wildcardCert)
	if cert, err := cfg.GetCertificate(helloSub); err != nil {
		t.Errorf("Didn't get wildcard cert, got: cert=%v, err=%v ", cert, err)
	} else if cert.Leaf.DNSNames[0] != "*.example.com" {
		t.Errorf("Got wrong certificate, expected wildcard: %v", cert)
	}

	// When cache is NOT empty but there's no SNI
	if _, err := cfg.GetCertificate(helloNoSNI); err == nil {
		t.Errorf("Expected TLS allert when no SNI and no DefaultServerName, but got: %v", err)
	}

	// When no certificate matches, raise an alert
	if _, err := cfg.GetCertificate(helloNoMatch); err == nil {
		t.Errorf("Expected an error when no certificate matched the SNI, got: %v", err)
	}

	// When default SNI is set and SNI is missing, retrieve default cert
	cfg.DefaultServerName = "example.com"
	if cert, err := cfg.GetCertificate(helloNoSNI); err != nil {
		t.Errorf("Got an error with no SNI with DefaultServerName, but shouldn't have: %v", err)
	} else if cert == nil || cert.Leaf.DNSNames[0] != "example.com" {
		t.Errorf("Expected default cert, got: %v", cert)
	}

	// When default SNI is set and SNI is missing but IP address matches, retrieve IP cert
	ipCert := Certificate{
		Names:       []string{"127.0.0.1"},
		Certificate: tls.Certificate{Leaf: &x509.Certificate{IPAddresses: []net.IP{net.ParseIP("127.0.0.1")}}},
		hash:        "(don't overwrite the first or second one)",
	}
	c.cacheCertificate(ipCert)
	if cert, err := cfg.GetCertificate(helloNoSNI); err != nil {
		t.Errorf("Got an error with no SNI but matching IP, but shouldn't have: %v", err)
	} else if cert == nil || len(cert.Leaf.IPAddresses) == 0 {
		t.Errorf("Expected IP cert, got: %v", cert)
	}
}

// TestGetCertDuringHandshakeWaiterErrorPropagation verifies that when the
// "leader" goroutine loading/obtaining a certificate for a name fails (e.g.
// an on-demand permission denial), the failure is propagated directly to all
// goroutines waiting on it. Without propagation, each waiter recursively
// re-enters the wait queue and eventually performs its own load/obtain
// attempt; under sustained handshake load for uncertificated names those
// recursing goroutines accumulate without bound, each pinning live TLS
// handshake state.
func TestGetCertDuringHandshakeWaiterErrorPropagation(t *testing.T) {
	const serverName = "denied.example.com"

	c := &Cache{
		cache:      make(map[string]Certificate),
		cacheIndex: make(map[string][]string),
		logger:     defaultTestLogger,
	}

	denyErr := errors.New("on-demand permission denied")
	release := make(chan struct{})
	var decisionCalls atomic.Int32
	cfg := &Config{
		Logger:    defaultTestLogger,
		certCache: c,
		OnDemand: &OnDemandConfig{
			DecisionFunc: func(ctx context.Context, name string) error {
				decisionCalls.Add(1)
				<-release // hold the leader so waiters queue behind it
				return denyErr
			},
		},
	}

	l, _ := net.Listen("tcp", "127.0.0.1:0")
	defer l.Close()
	conn, err := net.Dial("tcp", l.Addr().String())
	if err != nil {
		t.Fatalf("failed to create test connection: %v", err)
	}
	defer conn.Close()

	hello := &tls.ClientHelloInfo{ServerName: serverName, Conn: conn}
	ctx := context.Background()

	const numHandshakes = 5
	results := make(chan error, numHandshakes)

	// leader: takes the load slot for serverName and blocks in DecisionFunc
	go func() {
		_, err := cfg.getCertDuringHandshake(ctx, hello, true)
		results <- err
	}()

	// wait until the leader has registered itself in the wait queue
	for {
		certLoadWaitChansMu.Lock()
		_, registered := certLoadWaitChans[serverName]
		certLoadWaitChansMu.Unlock()
		if registered {
			break
		}
		time.Sleep(time.Millisecond)
	}

	// waiters: queue behind the leader
	for i := 1; i < numHandshakes; i++ {
		go func() {
			_, err := cfg.getCertDuringHandshake(ctx, hello, true)
			results <- err
		}()
	}

	// Wait until every handshake goroutine is PARKED — the waiters blocked
	// in the wait-queue select and the leader blocked on the release
	// channel in DecisionFunc — before releasing the leader. Merely being
	// inside getCertDuringHandshake isn't enough: a goroutine still in the
	// preamble would miss the wait queue once the leader's cleanup runs
	// and become a second leader.
	parked := func() (selecting, receiving int) {
		buf := make([]byte, 1<<20)
		stacks := string(buf[:runtime.Stack(buf, true)])
		for _, g := range strings.Split(stacks, "\n\n") {
			if !strings.Contains(g, ").getCertDuringHandshake(") {
				continue
			}
			if strings.Contains(g, "[select]") {
				selecting++
			} else if strings.Contains(g, "[chan receive]") {
				receiving++
			}
		}
		return
	}
	for {
		selecting, receiving := parked()
		if selecting >= numHandshakes-1 && receiving >= 1 {
			break
		}
		time.Sleep(time.Millisecond)
	}
	close(release) // leader now fails with denyErr

	for i := 0; i < numHandshakes; i++ {
		if err := <-results; err == nil || !strings.Contains(err.Error(), denyErr.Error()) {
			t.Errorf("expected deny error, got: %v", err)
		}
	}

	// The decision func must have been called exactly once: only the leader
	// reaches the permission check; waiters receive its propagated error
	// rather than recursing into their own load/obtain attempts.
	if got := decisionCalls.Load(); got != 1 {
		t.Errorf("expected exactly 1 decision-func call (leader only), got %d", got)
	}
}

// staticManager is a Manager that returns a fixed certificate and/or error.
type staticManager struct {
	cert  *tls.Certificate
	err   error
	calls atomic.Int32
}

func (m *staticManager) GetCertificate(ctx context.Context, hello *tls.ClientHelloInfo) (*tls.Certificate, error) {
	m.calls.Add(1)
	return m.cert, m.err
}

// externalCertFor returns a certificate based on testCertificate, but with
// the given SANs and validity window.
func externalCertFor(tb testing.TB, names []string, notBefore, notAfter time.Time) *tls.Certificate {
	tb.Helper()
	cert := testCertificate(tb)
	leaf := *cert.Leaf
	leaf.DNSNames = names
	leaf.NotBefore = notBefore
	leaf.NotAfter = notAfter
	cert.Leaf = &leaf
	return &cert
}

// TestExternalManagerAuthorization verifies that the on-demand authorization
// checks (DecisionFunc / host allowlist) are enforced before certificates
// from external Managers are accepted.
func TestExternalManagerAuthorization(t *testing.T) {
	newCfg := func(onDemand *OnDemandConfig) *Config {
		return &Config{
			Logger:    defaultTestLogger,
			certCache: &Cache{cache: make(map[string]Certificate), cacheIndex: make(map[string][]string), logger: defaultTestLogger},
			OnDemand:  onDemand,
		}
	}
	hello := &tls.ClientHelloInfo{ServerName: "example.com", Conn: testConn{}}
	now := time.Now()
	validCert := externalCertFor(t, []string{"example.com"}, now.Add(-time.Hour), now.Add(time.Hour))

	// A certificate from an external manager must not be accepted when the
	// DecisionFunc denies the name; the manager must not even be consulted.
	mgr := &staticManager{cert: validCert}
	cfg := newCfg(&OnDemandConfig{
		Managers: []Manager{mgr},
		DecisionFunc: func(ctx context.Context, name string) error {
			return fmt.Errorf("denied")
		},
	})
	if _, err := cfg.GetCertificate(hello); err == nil {
		t.Error("expected error when DecisionFunc denies name, got certificate")
	}
	if got := mgr.calls.Load(); got != 0 {
		t.Errorf("expected manager not to be consulted for denied name, got %d calls", got)
	}

	// Same, but enforced via the implicit host allowlist.
	mgr = &staticManager{cert: validCert}
	cfg = newCfg(&OnDemandConfig{
		Managers:      []Manager{mgr},
		hostAllowlist: map[string]struct{}{"other.example.com": {}},
	})
	if _, err := cfg.GetCertificate(hello); err == nil {
		t.Error("expected error when name is not in host allowlist, got certificate")
	}
	if got := mgr.calls.Load(); got != 0 {
		t.Errorf("expected manager not to be consulted for disallowed name, got %d calls", got)
	}
}

// TestExternalManagerCertificateConstraints verifies that certificates from
// external Managers are only served if they cover the requested server name
// and are currently valid.
func TestExternalManagerCertificateConstraints(t *testing.T) {
	newCfg := func(managers ...Manager) *Config {
		return &Config{
			Logger:    defaultTestLogger,
			certCache: &Cache{cache: make(map[string]Certificate), cacheIndex: make(map[string][]string), logger: defaultTestLogger},
			OnDemand:  &OnDemandConfig{Managers: managers},
		}
	}
	now := time.Now()
	validFrom, validTo := now.Add(-time.Hour), now.Add(time.Hour)

	for i, tc := range []struct {
		names     []string
		notBefore time.Time
		notAfter  time.Time
		sni       string
		expectErr bool
	}{
		{names: []string{"example.com"}, notBefore: validFrom, notAfter: validTo, sni: "example.com"},
		// multi-SAN certificate covering the SNI
		{names: []string{"other.com", "example.com"}, notBefore: validFrom, notAfter: validTo, sni: "example.com"},
		// wildcard certificate covering the SNI
		{names: []string{"*.example.com"}, notBefore: validFrom, notAfter: validTo, sni: "sub.example.com"},
		// certificate does not cover the SNI
		{names: []string{"other.com"}, notBefore: validFrom, notAfter: validTo, sni: "example.com", expectErr: true},
		// wildcard does not cover the bare domain
		{names: []string{"*.example.com"}, notBefore: validFrom, notAfter: validTo, sni: "example.com", expectErr: true},
		// expired certificate
		{names: []string{"example.com"}, notBefore: now.Add(-2 * time.Hour), notAfter: now.Add(-time.Hour), sni: "example.com", expectErr: true},
		// not-yet-valid certificate
		{names: []string{"example.com"}, notBefore: now.Add(time.Hour), notAfter: now.Add(2 * time.Hour), sni: "example.com", expectErr: true},
	} {
		mgr := &staticManager{cert: externalCertFor(t, tc.names, tc.notBefore, tc.notAfter)}
		cfg := newCfg(mgr)
		hello := &tls.ClientHelloInfo{ServerName: tc.sni, Conn: testConn{}}
		cert, err := cfg.GetCertificate(hello)
		if tc.expectErr {
			if err == nil {
				t.Errorf("test %d: expected error for names=%v sni=%s, got certificate", i, tc.names, tc.sni)
			}
			continue
		}
		if err != nil {
			t.Errorf("test %d: expected certificate for names=%v sni=%s, got error: %v", i, tc.names, tc.sni, err)
		} else if cert == nil || cert.Leaf == nil {
			t.Errorf("test %d: expected certificate for names=%v sni=%s, got nil", i, tc.names, tc.sni)
		}
	}
}

// TestExternalManagerErrorNoFallback verifies that an error from an external
// Manager aborts the handshake: later managers are not consulted, and no
// other certificate source is tried.
func TestExternalManagerErrorNoFallback(t *testing.T) {
	mgrErr := errors.New("manager is broken")
	errMgr := &staticManager{err: mgrErr}
	backupMgr := &staticManager{cert: externalCertFor(t, []string{"example.com"}, time.Now().Add(-time.Hour), time.Now().Add(time.Hour))}
	cfg := &Config{
		Logger:    defaultTestLogger,
		certCache: &Cache{cache: make(map[string]Certificate), cacheIndex: make(map[string][]string), logger: defaultTestLogger},
		OnDemand:  &OnDemandConfig{Managers: []Manager{errMgr, backupMgr}},
	}
	hello := &tls.ClientHelloInfo{ServerName: "example.com", Conn: testConn{}}
	_, err := cfg.GetCertificate(hello)
	if err == nil || !strings.Contains(err.Error(), mgrErr.Error()) {
		t.Errorf("expected manager error to be returned, got: %v", err)
	}
	if got := backupMgr.calls.Load(); got != 0 {
		t.Errorf("expected later managers not to be consulted after error, got %d calls", got)
	}
}

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

// TestNormalizedName verifies that every host identity - plain DNS names,
// internationalized domain names, wildcard names, and IPv4/IPv6 literals -
// canonicalizes to a single stable string. The handshake cache lookup path
// (getCertificateFromCache) and the issuance/storage/challenge path
// (getNameFromClientHello) must both derive the exact same identity from a
// ClientHello, otherwise a certificate obtained under one name cannot be
// found under the other (see the "two names" split between IDNA-punycode
// and the old lowercase-only normalization, and the hard failure of
// idna.Lookup.ToASCII on IPv6 literals' colons).
func TestNormalizedName(t *testing.T) {
	for i, test := range []struct {
		input  string
		expect string
	}{
		// plain DNS names: trimmed and lowercased
		{"example.com", "example.com"},
		{"  WWW.Example.COM  ", "www.example.com"},

		// internationalized domain names: always punycode, regardless of
		// whether the client sent Unicode or already-encoded ASCII
		{"bücher.example", "xn--bcher-kva.example"},
		{"BÜCHER.Example", "xn--bcher-kva.example"},
		{"xn--bcher-kva.example", "xn--bcher-kva.example"},
		// the non-1:1 Greek sigma case must use the Lookup profile mapping
		{"σςΣ.example", "xn--3xabb.example"},

		// wildcard names are valid managed identifiers even though the
		// Lookup profile rejects the '*' label
		{"*.example.com", "*.example.com"},
		{"*.bücher.example", "*.xn--bcher-kva.example"},

		// IPv4 literals pass through and are lowercased/trimmed
		{"192.0.2.1", "192.0.2.1"},
		{"  192.0.2.1  ", "192.0.2.1"},

		// IPv6 literals must NOT be fed to IDNA (colons are disallowed
		// rune points) but canonicalized through net.ParseIP instead
		{"2001:db8::1", "2001:db8::1"},
		{"2001:DB8::1", "2001:db8::1"},
		{"::1", "::1"},
		// bracketed or host:port forms reduce to the bare literal
		{"[2001:db8::1]", "2001:db8::1"},
		{"[2001:db8::1]:443", "2001:db8::1"},
		// zone/scope identifiers are not part of the host identity
		{"fe80::1%eth0", "fe80::1"},
	} {
		actual := normalizedName(test.input)
		if actual != test.expect {
			t.Errorf("Test %d: normalizedName(%q) = %q, want %q",
				i, test.input, actual, test.expect)
		}
	}
}

// TestNormalizedNameIsStable asserts the two handshake normalization paths
// agree, so a certificate cached under the issuance/storage identity can
// always be located by the in-memory cache lookup identity.
func TestNormalizedNameIsStable(t *testing.T) {
	cfg := &Config{Logger: defaultTestLogger}

	for _, sni := range []string{
		"example.com",
		"bücher.example",        // Unicode IDN straight from a client
		"xn--bcher-kva.example", // the same host, already punycode
		"2001:db8::1",           // IPv6 literal (colons break IDNA Lookup)
		"[2001:db8::1]",         // bracketed IPv6 literal
		"192.0.2.1",
	} {
		hello := &tls.ClientHelloInfo{ServerName: sni}
		issuanceName, err := cfg.getNameFromClientHello(hello)
		if err != nil {
			t.Errorf("getNameFromClientHello(%q) returned unexpected error: %v", sni, err)
			continue
		}
		cacheName := normalizedName(hello.ServerName)
		if issuanceName != cacheName {
			t.Errorf("identity split for SNI %q: issuance/challenge path uses %q but cache lookup uses %q",
				sni, issuanceName, cacheName)
		}
	}

	// an empty SNI with no DefaultServerName falls back to the connection's
	// local IP; with a nil conn it must yield an empty string rather than an
	// IDNA error, and with a DefaultServerName it must use the same canonical
	// identity as every other path
	if name, err := cfg.getNameFromClientHello(&tls.ClientHelloInfo{}); err != nil || name != "" {
		t.Errorf("empty SNI with nil conn: got name=%q err=%v, want empty name and no error", name, err)
	}
	cfg.DefaultServerName = "bücher.example"
	name, err := cfg.getNameFromClientHello(&tls.ClientHelloInfo{})
	if err != nil {
		t.Fatalf("getNameFromClientHello with DefaultServerName: %v", err)
	}
	if want := normalizedName(cfg.DefaultServerName); name != want {
		t.Errorf("DefaultServerName path: got %q, want %q", name, want)
	}
}

// TestGetCertificateFromCacheIDNAndIPv6 verifies the cache lookup path
// matches certificates by the same canonical identity used when they were
// issued and indexed: Unicode IDN SNIs match punycode-indexed certs, and
// IPv6 literal SNIs match IP-indexed certs instead of failing IDNA.
func TestGetCertificateFromCacheIDNAndIPv6(t *testing.T) {
	certCache := &Cache{cache: make(map[string]Certificate), cacheIndex: make(map[string][]string), logger: defaultTestLogger}
	cfg := &Config{Logger: defaultTestLogger, certCache: certCache}

	idnCert := Certificate{
		Names:       []string{"xn--bcher-kva.example"},
		Certificate: tls.Certificate{Leaf: &x509.Certificate{DNSNames: []string{"xn--bcher-kva.example"}}},
		hash:        "idn-cert",
	}
	ipv6Cert := Certificate{
		Names:       []string{"2001:db8::1"},
		Certificate: tls.Certificate{Leaf: &x509.Certificate{IPAddresses: []net.IP{net.ParseIP("2001:db8::1")}}},
		hash:        "ipv6-cert",
	}
	certCache.cacheCertificate(idnCert)
	certCache.cacheCertificate(ipv6Cert)

	// client sends the IDN in raw Unicode; the cert is indexed by punycode
	if cert, matched, defaulted := cfg.getCertificateFromCache(&tls.ClientHelloInfo{ServerName: "bücher.example"}); !matched || defaulted {
		t.Errorf("Unicode IDN SNI should match punycode-indexed cert, got matched=%v defaulted=%v cert=%v", matched, defaulted, cert.Names)
	}
	// client sends an IPv6 literal SNI; the cert is indexed by the bare IP
	if cert, matched, defaulted := cfg.getCertificateFromCache(&tls.ClientHelloInfo{ServerName: "2001:db8::1"}); !matched || defaulted {
		t.Errorf("IPv6 literal SNI should match IP-indexed cert, got matched=%v defaulted=%v cert=%v", matched, defaulted, cert.Names)
	}
	// bracketed/upper-case spellings are the same host identity
	if cert, matched, _ := cfg.getCertificateFromCache(&tls.ClientHelloInfo{ServerName: "2001:DB8::1"}); !matched {
		t.Errorf("upper-case IPv6 SNI should match, got %v", cert.Names)
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

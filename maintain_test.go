package certmagic

import (
	"context"
	"crypto/x509"
	"crypto/x509/pkix"
	"fmt"
	"math/big"
	"sync"
	"sync/atomic"
	"testing"
	"time"
)

// failingIssuer is a fake Issuer that always fails, simulating a CA
// challenge validation failure (e.g. because DNS is broken, as in
// caddyserver/caddy#7843). It counts how many times Issue was called so
// tests can assert on attempt cadence.
type failingIssuer struct {
	calls atomic.Int32
	err   error
}

func (fi *failingIssuer) Issue(ctx context.Context, csr *x509.CertificateRequest) (*IssuedCertificate, error) {
	fi.calls.Add(1)
	return nil, fi.err
}

func (fi *failingIssuer) IssuerKey() string { return "failing_test_issuer" }

// signalingFailIssuer reports when its first attempt has been made, then
// always fails.
type signalingFailIssuer struct {
	calls     atomic.Int32
	attempted chan struct{}
	once      sync.Once
	err       error
}

func (si *signalingFailIssuer) Issue(ctx context.Context, csr *x509.CertificateRequest) (*IssuedCertificate, error) {
	si.calls.Add(1)
	si.once.Do(func() { close(si.attempted) })
	return nil, si.err
}

func (si *signalingFailIssuer) IssuerKey() string { return "signaling_fail_test_issuer" }

// lockTrackingStorage records whether the certificate lock is currently held.
type lockTrackingStorage struct {
	*FileStorage
	mu     sync.Mutex
	locked bool
}

func (s *lockTrackingStorage) Lock(ctx context.Context, name string) error {
	if err := s.FileStorage.Lock(ctx, name); err != nil {
		return err
	}
	s.mu.Lock()
	s.locked = true
	s.mu.Unlock()
	return nil
}

func (s *lockTrackingStorage) Unlock(ctx context.Context, name string) error {
	err := s.FileStorage.Unlock(ctx, name)
	s.mu.Lock()
	s.locked = false
	s.mu.Unlock()
	return err
}

func (s *lockTrackingStorage) isLocked() bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.locked
}

// TestQueueRenewalTaskPacesRetriesItself is a regression test for
// caddyserver/caddy#7843: after a transient failure (e.g. a DNS outage)
// prevented renewal, the certificate did not get renewed again even after
// the underlying problem cleared, until the process was restarted.
//
// Root cause: queueRenewalTask used to submit a job to the package-level
// jm that internally looped through doWithRetry's retryIntervals schedule
// for up to maxRetryDuration (30 days) without returning. Because jm.Submit
// silently drops duplicate submissions for a name that is already
// in-flight, every subsequent periodic maintenance tick's call to
// queueRenewalTask for the same certificate was a silent no-op: the only
// thing actually driving retries was the single long-lived job's own
// internal sleep, which could be up to 6 hours between attempts, and,
// depending on scheduling, could appear to simply stop making progress.
//
// This test simulates two consecutive maintenance ticks in quick
// succession for a certificate whose issuer always fails, and asserts:
//  1. The first tick makes exactly one renewal attempt.
//  2. A second tick immediately afterward makes NO additional attempt,
//     because we are intentionally backing off (this is desired -- we
//     don't want to hammer the CA every RenewCheckInterval).
//  3. Once the backoff interval has elapsed, a third tick DOES make
//     another attempt -- proving that renewal attempts are paced by an
//     externally observable, bounded schedule (retryIntervals[0], on the
//     order of a minute) rather than being silently stuck behind a
//     multi-hour-or-longer sleep inside a single dedup-protected job.
func TestQueueRenewalTaskPacesRetriesItself(t *testing.T) {
	const domain = "example.com"
	issuer := &failingIssuer{err: fmt.Errorf("simulated DNS-01 challenge failure")}

	certCache := &Cache{
		cache:      make(map[string]Certificate),
		cacheIndex: make(map[string][]string),
		logger:     defaultTestLogger,
	}
	cfg := &Config{
		Issuers:          []Issuer{issuer},
		Storage:          &FileStorage{Path: t.TempDir()},
		Logger:           defaultTestLogger,
		DisableARI:       true, // keep the renewal-needed check to plain expiration logic
		ReusePrivateKeys: true, // avoid needing a KeySource for a fresh key
		certCache:        certCache,
	}
	cfg.OCSP.DisableStapling = true

	// Build an already-expired self-signed leaf certificate and stash it in
	// storage as the "current" cert resource, so loadCertResourceAnyIssuer
	// finds something to renew.
	tmpl := &x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject:      pkix.Name{CommonName: domain},
		DNSNames:     []string{domain},
		NotBefore:    time.Now().Add(-60 * 24 * time.Hour),
		NotAfter:     time.Now().Add(-1 * time.Hour), // already expired
	}
	leaf, priv, certPEM := mustIssueTestCertificate(t, tmpl, nil, nil)

	privPEM, err := PEMEncodePrivateKey(priv)
	if err != nil {
		t.Fatalf("encoding private key: %v", err)
	}

	certRes := CertificateResource{
		SANs:           []string{domain},
		CertificatePEM: certPEM,
		PrivateKeyPEM:  privPEM,
		issuerKey:      issuer.IssuerKey(),
	}
	ctx := context.Background()
	if err := cfg.saveCertResource(ctx, issuer, certRes); err != nil {
		t.Fatalf("seeding cert resource in storage: %v", err)
	}

	oldCert := Certificate{
		Names:     []string{domain},
		managed:   true,
		issuerKey: issuer.IssuerKey(),
	}
	oldCert.Leaf = leaf

	jobName := "renew_" + domain
	// Make sure we start from a clean slate in the shared package-level
	// schedule, in case another test left state behind.
	renewalRetrySchedule.clear(jobName)
	t.Cleanup(func() { renewalRetrySchedule.clear(jobName) })

	// --- Tick 1: should make exactly one attempt, then back off. ---
	if err := certCache.queueRenewalTask(ctx, oldCert, cfg); err != nil {
		t.Fatalf("queueRenewalTask (tick 1): %v", err)
	}
	if !waitUntil(time.Second, func() bool { return issuer.calls.Load() == 1 }) {
		t.Fatalf("expected exactly 1 issuance attempt after tick 1, got %d", issuer.calls.Load())
	}
	// Give the job's error-handling path (which calls
	// renewalRetrySchedule.recordFailure) a moment to run after Issue
	// returns, since it happens in the jobManager worker goroutine.
	if !waitUntil(time.Second, func() bool { return !renewalRetrySchedule.readyFor(jobName) }) {
		t.Fatal("expected renewal name to be backing off after a failed attempt")
	}

	// --- Tick 2: fires immediately after tick 1; must NOT attempt again,
	// because we are still within the first backoff interval. This is the
	// crux of the fix: previously it was jm's dedup (silent, unbounded)
	// doing this job; now it's an explicit, bounded backoff check. ---
	if err := certCache.queueRenewalTask(ctx, oldCert, cfg); err != nil {
		t.Fatalf("queueRenewalTask (tick 2): %v", err)
	}
	time.Sleep(50 * time.Millisecond) // give any (unwanted) job a chance to run
	if got := issuer.calls.Load(); got != 1 {
		t.Fatalf("expected still only 1 issuance attempt immediately after tick 2 (should be backing off), got %d", got)
	}

	// --- Simulate the backoff interval elapsing by directly rewinding the
	// recorded schedule (equivalent to waiting retryIntervals[0], which we
	// don't want this test to actually spend real time on). ---
	renewalRetrySchedule.mu.Lock()
	if st, ok := renewalRetrySchedule.state[jobName]; ok {
		st.nextAttempt = time.Now().Add(-time.Millisecond)
	} else {
		t.Fatal("expected backoff state to be recorded for job name")
	}
	renewalRetrySchedule.mu.Unlock()

	// --- Tick 3: backoff has elapsed, so this tick must retry. ---
	if err := certCache.queueRenewalTask(ctx, oldCert, cfg); err != nil {
		t.Fatalf("queueRenewalTask (tick 3): %v", err)
	}
	if !waitUntil(time.Second, func() bool { return issuer.calls.Load() == 2 }) {
		t.Fatalf("expected a second issuance attempt once the backoff interval elapsed, got %d", issuer.calls.Load())
	}
}

// TestManageOneAsyncDoesNotHoldRenewalJob verifies that asynchronous
// management does not submit a renewal job that camps on the jobManager's
// dedup slot for the whole retry budget. A failing attempt must return and
// release the name so the periodic maintenance loop can pace the next attempt.
func TestManageOneAsyncDoesNotHoldRenewalJob(t *testing.T) {
	const domain = "manage-async.example.com"
	issuer := &failingIssuer{err: fmt.Errorf("simulated renewal failure")}

	certCache := &Cache{
		cache:      make(map[string]Certificate),
		cacheIndex: make(map[string][]string),
		logger:     defaultTestLogger,
	}
	cfg := &Config{
		Issuers:          []Issuer{issuer},
		Storage:          &FileStorage{Path: t.TempDir()},
		Logger:           defaultTestLogger,
		DisableARI:       true,
		ReusePrivateKeys: true,
		certCache:        certCache,
	}
	cfg.OCSP.DisableStapling = true

	tmpl := &x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject:      pkix.Name{CommonName: domain},
		DNSNames:     []string{domain},
		NotBefore:    time.Now().Add(-60 * 24 * time.Hour),
		NotAfter:     time.Now().Add(-time.Hour),
	}
	_, priv, certPEM := mustIssueTestCertificate(t, tmpl, nil, nil)
	privPEM, err := PEMEncodePrivateKey(priv)
	if err != nil {
		t.Fatalf("encoding private key: %v", err)
	}
	certRes := CertificateResource{
		SANs:           []string{domain},
		CertificatePEM: certPEM,
		PrivateKeyPEM:  privPEM,
		issuerKey:      issuer.IssuerKey(),
	}
	ctx := context.Background()
	if err := cfg.saveCertResource(ctx, issuer, certRes); err != nil {
		t.Fatalf("seeding cert resource in storage: %v", err)
	}
	jobName := "renew_" + domain
	renewalRetrySchedule.clear(jobName)
	t.Cleanup(func() { renewalRetrySchedule.clear(jobName) })

	if err := cfg.manageOne(ctx, domain, true); err != nil {
		t.Fatalf("manageOne (async): %v", err)
	}
	if !waitUntil(time.Second, func() bool { return issuer.calls.Load() == 1 }) {
		t.Fatalf("expected one issuance attempt, got %d", issuer.calls.Load())
	}

	jm.mu.Lock()
	_, inFlight := jm.names[jobName]
	jm.mu.Unlock()
	if inFlight {
		t.Fatal("renewal job should not remain in flight after a single failed attempt")
	}

	// A second async management pass must not launch another competing job
	// while the renewal backoff is active.
	if err := cfg.manageOne(ctx, domain, true); err != nil {
		t.Fatalf("manageOne (async, second pass): %v", err)
	}
	time.Sleep(50 * time.Millisecond)
	if got := issuer.calls.Load(); got != 1 {
		t.Fatalf("expected no additional attempt during backoff, got %d", got)
	}
}

// TestRenewCertReleasesLockBetweenRetries verifies that a failing renewal
// does not hold the storage lock while waiting to retry. Holding it across the
// whole retry budget would make the certificate permanently occupied by one
// failing task, preventing other instances (or the maintenance loop) from
// renewing it even after the original problem is resolved.
func TestRenewCertReleasesLockBetweenRetries(t *testing.T) {
	const domain = "lock-between-retries.example.com"
	issuer := &signalingFailIssuer{
		attempted: make(chan struct{}),
		err:       fmt.Errorf("simulated issuance failure"),
	}
	storage := &lockTrackingStorage{FileStorage: &FileStorage{Path: t.TempDir()}}
	cfg := &Config{
		Issuers:          []Issuer{issuer},
		Storage:          storage,
		Logger:           defaultTestLogger,
		DisableARI:       true,
		ReusePrivateKeys: true,
		certCache: &Cache{
			cache:      make(map[string]Certificate),
			cacheIndex: make(map[string][]string),
			logger:     defaultTestLogger,
		},
	}
	cfg.OCSP.DisableStapling = true

	tmpl := &x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject:      pkix.Name{CommonName: domain},
		DNSNames:     []string{domain},
		NotBefore:    time.Now().Add(-60 * 24 * time.Hour),
		NotAfter:     time.Now().Add(-time.Hour),
	}
	_, priv, certPEM := mustIssueTestCertificate(t, tmpl, nil, nil)
	privPEM, err := PEMEncodePrivateKey(priv)
	if err != nil {
		t.Fatalf("encoding private key: %v", err)
	}
	certRes := CertificateResource{
		SANs:           []string{domain},
		CertificatePEM: certPEM,
		PrivateKeyPEM:  privPEM,
		issuerKey:      issuer.IssuerKey(),
	}
	ctx := context.Background()
	if err := cfg.saveCertResource(ctx, issuer, certRes); err != nil {
		t.Fatalf("seeding cert resource in storage: %v", err)
	}

	// Give the first attempt ample time, but cancel before the retry fires.
	originalIntervals := retryIntervals
	retryIntervals = []time.Duration{time.Hour}
	t.Cleanup(func() { retryIntervals = originalIntervals })

	renewCtx, cancelRenew := context.WithCancel(ctx)
	done := make(chan struct{})
	go func() {
		_ = cfg.RenewCertAsync(renewCtx, domain, false)
		close(done)
	}()
	t.Cleanup(func() {
		cancelRenew()
		<-done
	})

	select {
	case <-issuer.attempted:
	case <-time.After(2 * time.Second):
		t.Fatal("renewal never made its first attempt")
	}
	if !waitUntil(time.Second, func() bool { return !storage.isLocked() }) {
		t.Fatal("renewal lock was not released after the failed attempt")
	}

	// Prove the lock is actually available while the renewal is backing off.
	lockKey := cfg.lockKey(certIssueLockOp, domain)
	lockCtx, cancelLock := context.WithTimeout(ctx, 500*time.Millisecond)
	if err := acquireLock(lockCtx, storage, lockKey); err != nil {
		cancelLock()
		t.Fatalf("could not acquire renewal lock during backoff: %v", err)
	}
	cancelLock()
	if err := releaseLock(ctx, storage, lockKey); err != nil {
		t.Fatalf("releasing test lock: %v", err)
	}

	cancelRenew()
	select {
	case <-done:
	case <-time.After(2 * time.Second):
		t.Fatal("renewal did not stop after context cancellation")
	}
}

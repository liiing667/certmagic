// Copyright 2015 Matthew Holt
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package certmagic

import (
	"bufio"
	"bytes"
	"context"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"unsafe"

	"github.com/mholt/acmez/v3/acme"
	"go.uber.org/zap"
)

// getAccountToUse will either load or create an account based on the configuration of the issuer.
// It will try to get one from storage if one exists, and if not, it will create one, all the while
// honoring the configured account key PEM (if any) to restrict which account is used.
func (iss *ACMEIssuer) getAccountToUse(ctx context.Context, directory string) (acme.Account, error) {
	email := iss.getEmail()
	keyPEM := []byte(iss.AccountKeyPEM)
	cacheKey := iss.accountCacheKey(directory, email, keyPEM)

	// Account lookups happen for every issuance and renewal. A cheap,
	// read-mostly cache avoids stampeding storage (and, worse, the ACME
	// server) when many certificates are managed at once. Only accounts
	// known to be durable (registered, or loaded from storage) are cached;
	// a freshly generated unregistered key must not be mistaken for the
	// durable account identity.
	if account, ok := iss.cachedAccount(cacheKey); ok {
		return account, nil
	}

	return iss.loadAccountShared(ctx, cacheKey, directory, email, keyPEM)
}

// loadAccountShared loads (or creates) one account per cache key at a time.
// Concurrent callers for the same CA/account identity wait for the first
// caller and share its outcome, so they cannot each create a different
// account key or overwrite each other's account registration.
func (iss *ACMEIssuer) loadAccountShared(ctx context.Context, cacheKey acmeAccountCacheKey, directory, email string, keyPEM []byte) (account acme.Account, err error) {
	store := iss.accountStore()

	store.loadsMu.Lock()
	if load, ok := store.loads[cacheKey]; ok {
		store.loadsMu.Unlock()
		select {
		case <-ctx.Done():
			return acme.Account{}, ctx.Err()
		case <-load.done:
			return load.account, load.err
		}
	}
	load := &acmeAccountLoad{done: make(chan struct{})}
	store.loads[cacheKey] = load
	store.loadsMu.Unlock()

	finished := false
	defer func() {
		// Always release waiters, even if loading panics. A waiter must never
		// be stranded on a channel that nobody will close.
		if !finished {
			if err == nil {
				err = fmt.Errorf("loading ACME account was aborted")
			}
			account = acme.Account{}
		}

		store.loadsMu.Lock()
		load.account, load.err = account, err
		close(load.done)
		delete(store.loads, cacheKey)
		store.loadsMu.Unlock()
	}()

	if len(keyPEM) > 0 {
		iss.Logger.Info("using configured ACME account")
		account, err = iss.GetAccount(ctx, keyPEM)
	} else {
		account, err = iss.loadOrCreateAccount(ctx, directory, email)
	}
	if err != nil {
		err = fmt.Errorf("getting ACME account: %v", err)
	} else {
		// Prefer an account that a concurrent registration/save already
		// published; otherwise cache a registered account now.
		if cached, ok := iss.cachedAccount(cacheKey); ok {
			account = cached
		} else if account.Status != "" {
			iss.cacheLoadedAccount(cacheKey, account)
			if cached, ok := iss.cachedAccount(cacheKey); ok {
				account = cached
			}
		}
	}

	finished = true
	return account, err
}

// loadOrCreateAccount either loads or creates a new account, depending on if
// an account can be found in storage for the given CA + email combo.
func (am *ACMEIssuer) loadOrCreateAccount(ctx context.Context, ca, email string) (acme.Account, error) {
	acct, err := am.loadAccount(ctx, ca, email)
	if err == nil {
		// An account read from storage is durable even if its status field is
		// empty (for example, an older registration file). Cache it so
		// concurrent callers do not each reload it and create a different
		// pending account key.
		am.cachePersistedAccount(am.accountCacheKey(ca, email, nil), acct)
	}
	if errors.Is(err, fs.ErrNotExist) {
		am.Logger.Info("creating new account because no account for configured email is known to us",
			zap.String("email", email),
			zap.String("ca", ca),
			zap.Error(err))
		return am.newAccount(email)
	}
	am.Logger.Debug("using existing ACME account because key found in storage associated with email",
		zap.String("email", email),
		zap.String("ca", ca))
	return acct, err
}

// loadAccount loads an account from storage, but does not create a new one.
func (am *ACMEIssuer) loadAccount(ctx context.Context, ca, email string) (acme.Account, error) {
	var regBytes, keyBytes []byte
	err := func() error {
		// account registration writes the registration and private key as a
		// pair; use the same read/write lock as saveAccount so a reader cannot
		// observe a registration from one account with the private key from
		// another during a concurrent update.
		acmeAccountStoreMu.RLock()
		defer acmeAccountStoreMu.RUnlock()

		var err error
		regBytes, err = am.config.Storage.Load(ctx, am.storageKeyUserReg(ca, email))
		if err != nil {
			return err
		}
		keyBytes, err = am.config.Storage.Load(ctx, am.storageKeyUserPrivateKey(ca, email))
		return err
	}()
	if err != nil {
		return acme.Account{}, err
	}

	var acct acme.Account
	err = json.Unmarshal(regBytes, &acct)
	if err != nil {
		return acct, err
	}
	acct.PrivateKey, err = PEMDecodePrivateKey(keyBytes)
	if err != nil {
		return acct, fmt.Errorf("could not decode account's private key: %v", err)
	}

	return acct, nil
}

// newAccount generates a new private key for a new ACME account, but
// it does not register or save the account.
func (*ACMEIssuer) newAccount(email string) (acme.Account, error) {
	var acct acme.Account
	if email != "" {
		acct.Contact = []string{"mailto:" + email} // TODO: should we abstract the contact scheme?
	}
	privateKey, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return acct, fmt.Errorf("generating private key: %v", err)
	}
	acct.PrivateKey = privateKey
	return acct, nil
}

// GetAccount first tries loading the account with the associated private key from storage.
// If it does not exist in storage, it will be retrieved from the ACME server and added to storage.
// The account must already exist; it does not create a new account.
func (am *ACMEIssuer) GetAccount(ctx context.Context, privateKeyPEM []byte) (acme.Account, error) {
	email := am.getEmail()
	if email == "" {
		if account, err := am.loadAccountByKey(ctx, privateKeyPEM); err == nil {
			return account, nil
		}
	} else {
		keyBytes, err := am.config.Storage.Load(ctx, am.storageKeyUserPrivateKey(am.CA, email))
		if err == nil && bytes.Equal(bytes.TrimSpace(keyBytes), bytes.TrimSpace(privateKeyPEM)) {
			return am.loadAccount(ctx, am.CA, email)
		}
	}
	return am.lookUpAccount(ctx, privateKeyPEM)
}

// loadAccountByKey loads the account with the given private key from storage, if it exists.
// If it does not exist, an error of type fs.ErrNotExist is returned. This is not very efficient
// for lots of accounts.
func (am *ACMEIssuer) loadAccountByKey(ctx context.Context, privateKeyPEM []byte) (acme.Account, error) {
	accountList, err := am.config.Storage.List(ctx, am.storageKeyUsersPrefix(am.CA), false)
	if err != nil {
		return acme.Account{}, err
	}
	for _, accountFolderKey := range accountList {
		email := path.Base(accountFolderKey)
		keyBytes, err := am.config.Storage.Load(ctx, am.storageKeyUserPrivateKey(am.CA, email))
		if err != nil {
			// Try the next account: This one is missing its private key, if it turns out to be the one we're looking
			// for we will try to save it again after confirming with the ACME server.
			continue
		}
		if bytes.Equal(bytes.TrimSpace(keyBytes), bytes.TrimSpace(privateKeyPEM)) {
			// Found the account with the correct private key, try loading it. If this fails we we will follow
			// the same procedure as if the private key was not found and confirm with the ACME server before saving
			// it again.
			return am.loadAccount(ctx, am.CA, email)
		}
	}
	return acme.Account{}, fs.ErrNotExist
}

// lookUpAccount looks up the account associated with privateKeyPEM from the ACME server.
// If the account is found by the server, it will be saved to storage and returned.
func (am *ACMEIssuer) lookUpAccount(ctx context.Context, privateKeyPEM []byte) (acme.Account, error) {
	client, err := am.newACMEClient(false)
	if err != nil {
		return acme.Account{}, fmt.Errorf("creating ACME client: %v", err)
	}

	privateKey, err := PEMDecodePrivateKey([]byte(privateKeyPEM))
	if err != nil {
		return acme.Account{}, fmt.Errorf("decoding private key: %v", err)
	}

	// look up the account
	account := acme.Account{PrivateKey: privateKey}
	account, err = client.GetAccount(ctx, account)
	if err != nil {
		return acme.Account{}, fmt.Errorf("looking up account with server: %v", err)
	}

	// save the account details to storage
	err = am.saveAccount(ctx, client.Directory, account)
	if err != nil {
		return account, fmt.Errorf("could not save account to storage: %v", err)
	}

	return account, nil
}

// saveAccount persists an ACME account's info and private key to storage.
// It does NOT register the account via ACME or prompt the user.
func (am *ACMEIssuer) saveAccount(ctx context.Context, ca string, account acme.Account) error {
	regBytes, err := json.MarshalIndent(account, "", "\t")
	if err != nil {
		return err
	}
	keyBytes, err := PEMEncodePrivateKey(account.PrivateKey)
	if err != nil {
		return err
	}
	// extract primary contact (email), without scheme (e.g. "mailto:")
	primaryContact := getPrimaryContact(account)
	all := []keyValue{
		{
			key:   am.storageKeyUserReg(ca, primaryContact),
			value: regBytes,
		},
		{
			key:   am.storageKeyUserPrivateKey(ca, primaryContact),
			value: keyBytes,
		},
	}

	// Serialize the two-file account update. Without this, concurrent
	// registrations for the same account identity can interleave their
	// writes, leaving the registration from one account paired with the
	// private key from another. Renewal then signs with a different
	// principal than the account it thinks it is using.
	acmeAccountStoreMu.Lock()
	defer acmeAccountStoreMu.Unlock()

	if err := storeTx(ctx, am.config.Storage, all); err != nil {
		return err
	}

	// Keep the in-memory cache coherent with storage while still holding
	// the update lock, so another goroutine cannot reload a stale account
	// between the write and the cache update.
	am.cacheAccount(am.accountCacheKey(ca, primaryContact, nil), account)
	return nil
}

// deleteAccountLocally deletes the registration info and private key of the account
// for the given CA from storage.
func (am *ACMEIssuer) deleteAccountLocally(ctx context.Context, ca string, account acme.Account) error {
	primaryContact := getPrimaryContact(account)

	acmeAccountStoreMu.Lock()
	defer acmeAccountStoreMu.Unlock()

	// Invalidate cached account state even if a delete fails partway
	// through; otherwise a later attempt could keep reusing an account that
	// no longer exists remotely.
	am.invalidateAccountCache(ca)

	if err := am.config.Storage.Delete(ctx, am.storageKeyUserReg(ca, primaryContact)); err != nil {
		return err
	}
	return am.config.Storage.Delete(ctx, am.storageKeyUserPrivateKey(ca, primaryContact))
}

// setEmail does everything it can to obtain an email address
// from the user within the scope of memory and storage to use
// for ACME TLS. If it cannot get an email address, it does nothing
// (If user is prompted, it will warn the user of
// the consequences of an empty email.) This function MAY prompt
// the user for input. If allowPrompts is false, the user
// will NOT be prompted and an empty email may be returned.
func (am *ACMEIssuer) setEmail(ctx context.Context, allowPrompts bool) error {
	leEmail := am.Email

	// First try package default email, or a discovered email address
	if leEmail == "" {
		leEmail = DefaultACME.Email
	}
	if leEmail == "" {
		discoveredEmailMu.Lock()
		leEmail = discoveredEmail
		discoveredEmailMu.Unlock()
	}

	// Then try to get most recent user email from storage
	var gotRecentEmail bool
	if leEmail == "" {
		leEmail, gotRecentEmail = am.mostRecentAccountEmail(ctx, am.CA)
	}
	if !gotRecentEmail && leEmail == "" && allowPrompts {
		// Looks like there is no email address readily available,
		// so we will have to ask the user if we can.
		var err error
		leEmail, err = am.promptUserForEmail()
		if err != nil {
			return err
		}

		// User might have just signified their agreement
		am.mu.Lock()
		am.agreed = DefaultACME.Agreed
		am.mu.Unlock()
	}

	// Save the email for later and ensure it is consistent
	// for repeated use; then update cfg with the email
	leEmail = strings.TrimSpace(strings.ToLower(leEmail))
	discoveredEmailMu.Lock()
	if discoveredEmail == "" {
		discoveredEmail = leEmail
	}
	discoveredEmailMu.Unlock()

	// The unexported email field is the one we use
	// because we have thread-safe control over it
	am.mu.Lock()
	am.email = leEmail
	am.mu.Unlock()

	return nil
}

// promptUserForEmail prompts the user for an email address
// and returns the email address they entered (which could
// be the empty string). If no error is returned, then Agreed
// will also be set to true, since continuing through the
// prompt signifies agreement.
func (am *ACMEIssuer) promptUserForEmail() (string, error) {
	// prompt the user for an email address and terms agreement
	reader := bufio.NewReader(stdin)
	am.promptUserAgreement("")
	fmt.Println("Please enter your email address to signify agreement and to be notified")
	fmt.Println("in case of issues. You can leave it blank, but we don't recommend it.")
	fmt.Print("  Email address: ")
	leEmail, err := reader.ReadString('\n')
	if err != nil && err != io.EOF {
		return "", fmt.Errorf("reading email address: %v", err)
	}
	leEmail = strings.TrimSpace(leEmail)
	DefaultACME.Agreed = true
	return leEmail, nil
}

// promptUserAgreement simply outputs the standard user
// agreement prompt with the given agreement URL.
// It outputs a newline after the message.
func (am *ACMEIssuer) promptUserAgreement(agreementURL string) {
	userAgreementPrompt := `Your sites will be served over HTTPS automatically using an automated CA.
By continuing, you agree to the CA's terms of service`
	if agreementURL == "" {
		fmt.Printf("\n\n%s.\n", userAgreementPrompt)
		return
	}
	fmt.Printf("\n\n%s at:\n  %s\n", userAgreementPrompt, agreementURL)
}

// askUserAgreement prompts the user to agree to the agreement
// at the given agreement URL via stdin. It returns whether the
// user agreed or not.
func (am *ACMEIssuer) askUserAgreement(agreementURL string) bool {
	am.promptUserAgreement(agreementURL)
	fmt.Print("Do you agree to the terms? (y/n): ")

	reader := bufio.NewReader(stdin)
	answer, err := reader.ReadString('\n')
	if err != nil {
		return false
	}
	answer = strings.ToLower(strings.TrimSpace(answer))

	return answer == "y" || answer == "yes"
}

func storageKeyACMECAPrefix(issuerKey string) string {
	return path.Join(prefixACME, StorageKeys.Safe(issuerKey))
}

func (am *ACMEIssuer) storageKeyCAPrefix(caURL string) string {
	return storageKeyACMECAPrefix(am.issuerKey(caURL))
}

func (am *ACMEIssuer) storageKeyUsersPrefix(caURL string) string {
	return path.Join(am.storageKeyCAPrefix(caURL), "users")
}

func (am *ACMEIssuer) storageKeyUserPrefix(caURL, email string) string {
	if email == "" {
		email = emptyEmail
	}
	return path.Join(am.storageKeyUsersPrefix(caURL), StorageKeys.Safe(email))
}

func (am *ACMEIssuer) storageKeyUserReg(caURL, email string) string {
	return am.storageSafeUserKey(caURL, email, "registration", ".json")
}

func (am *ACMEIssuer) storageKeyUserPrivateKey(caURL, email string) string {
	return am.storageSafeUserKey(caURL, email, "private", ".key")
}

// storageSafeUserKey returns a key for the given email, with the default
// filename, and the filename ending in the given extension.
func (am *ACMEIssuer) storageSafeUserKey(ca, email, defaultFilename, extension string) string {
	if email == "" {
		email = emptyEmail
	}
	email = strings.ToLower(email)
	filename := am.emailUsername(email)
	if filename == "" {
		filename = defaultFilename
	}
	filename = StorageKeys.Safe(filename)
	return path.Join(am.storageKeyUserPrefix(ca, email), filename+extension)
}

// emailUsername returns the username portion of an email address (part before
// '@') or the original input if it can't find the "@" symbol.
func (*ACMEIssuer) emailUsername(email string) string {
	at := strings.Index(email, "@")
	if at == -1 {
		return email
	} else if at == 0 {
		return email[1:]
	}
	return email[:at]
}

// mostRecentAccountEmail finds the most recently-written account file
// in storage. Since this is part of a complex sequence to get a user
// account, errors here are discarded to simplify code flow in
// the caller, and errors are not important here anyway.
func (am *ACMEIssuer) mostRecentAccountEmail(ctx context.Context, caURL string) (string, bool) {
	accountList, err := am.config.Storage.List(ctx, am.storageKeyUsersPrefix(caURL), false)
	if err != nil || len(accountList) == 0 {
		return "", false
	}

	// get all the key infos ahead of sorting, because
	// we might filter some out
	stats := make(map[string]KeyInfo)
	for i := 0; i < len(accountList); i++ {
		u := accountList[i]
		keyInfo, err := am.config.Storage.Stat(ctx, u)
		if err != nil {
			continue
		}
		if keyInfo.IsTerminal {
			// I found a bug when macOS created a .DS_Store file in
			// the users folder, and CertMagic tried to use that as
			// the user email because it was newer than the other one
			// which existed... sure, this isn't a perfect fix but
			// frankly one's OS shouldn't mess with the data folder
			// in the first place.
			accountList = append(accountList[:i], accountList[i+1:]...)
			i--
			continue
		}
		stats[u] = keyInfo
	}

	sort.Slice(accountList, func(i, j int) bool {
		iInfo := stats[accountList[i]]
		jInfo := stats[accountList[j]]
		return jInfo.Modified.Before(iInfo.Modified)
	})

	if len(accountList) == 0 {
		return "", false
	}

	account, err := am.loadOrCreateAccount(ctx, caURL, path.Base(accountList[0]))
	if err != nil {
		return "", false
	}

	return getPrimaryContact(account), true
}

func accountRegLockKey(acc acme.Account) string {
	key := "register_acme_account"
	if len(acc.Contact) == 0 {
		return key
	}
	key += "_" + getPrimaryContact(acc)
	return key
}

// getPrimaryContact returns the first contact on the account (if any)
// without the scheme. (I guess we assume an email address.)
func getPrimaryContact(account acme.Account) string {
	// TODO: should this be abstracted with some lower-level helper?
	var primaryContact string
	if len(account.Contact) > 0 {
		primaryContact = account.Contact[0]
		if idx := strings.Index(primaryContact, ":"); idx >= 0 {
			primaryContact = primaryContact[idx+1:]
		}
	}
	return primaryContact
}

// acmeAccountCacheKey identifies a single durable ACME account. The storage
// identity is part of the key so that two independent Configs using different
// storage backends never share an account by accident. The configured account
// key (when present) is part of the key as well, because it pins the identity
// even if an email is configured or discovered later.
type acmeAccountCacheKey struct {
	storage    string
	directory  string
	email      string
	accountKey string
}

type acmeAccountLoad struct {
	done    chan struct{}
	account acme.Account
	err     error
}

// acmeAccountStore holds this issuer's cached accounts and coalesces
// concurrent misses. Keeping it per-issuer avoids sharing account state
// between unrelated Configs (and between short-lived issuers in tests) while
// still allowing the account to be reused for every renewal.
type acmeAccountStore struct {
	mu       sync.RWMutex
	accounts map[acmeAccountCacheKey]acme.Account

	loadsMu sync.Mutex
	loads   map[acmeAccountCacheKey]*acmeAccountLoad
}

var (
	// acmeAccountRegLocks serializes account registration in this process,
	// independently of the storage backend's Lock implementation. Storage
	// locks remain the cross-process coordination mechanism; this one makes
	// the single-account guarantee hold even for storages whose Lock is a
	// no-op or has a coarser scope.
	acmeAccountRegLocks sync.Map // map[string]*sync.Mutex

	// acmeAccountStoreMu keeps the multi-file account registration in
	// storage consistent with the in-memory cache. Account writes are rare;
	// reads of an already-cached account never take this lock.
	acmeAccountStoreMu sync.RWMutex
)

func lockAccountRegistration(key string) func() {
	mu, _ := acmeAccountRegLocks.LoadOrStore(key, new(sync.Mutex))
	mutex := mu.(*sync.Mutex)
	mutex.Lock()
	return mutex.Unlock
}

func (iss *ACMEIssuer) accountStore() *acmeAccountStore {
	if store := atomic.LoadPointer(&iss.acmeAccounts); store != nil {
		return (*acmeAccountStore)(store)
	}

	store := &acmeAccountStore{
		accounts: make(map[acmeAccountCacheKey]acme.Account),
		loads:    make(map[acmeAccountCacheKey]*acmeAccountLoad),
	}
	if atomic.CompareAndSwapPointer(&iss.acmeAccounts, nil, unsafe.Pointer(store)) {
		return store
	}
	return (*acmeAccountStore)(atomic.LoadPointer(&iss.acmeAccounts))
}

func (iss *ACMEIssuer) accountCacheKey(directory, email string, keyPEM []byte) acmeAccountCacheKey {
	storageID := ""
	if iss.config != nil && iss.config.Storage != nil {
		storageID = fmt.Sprintf("%T:%p", iss.config.Storage, iss.config.Storage)
	}
	keyID := ""
	if len(keyPEM) > 0 {
		keyID = string(keyPEM)
	}
	return acmeAccountCacheKey{
		storage:    storageID,
		directory:  directory,
		email:      strings.ToLower(strings.TrimSpace(email)),
		accountKey: keyID,
	}
}

func (iss *ACMEIssuer) cachedAccount(key acmeAccountCacheKey) (acme.Account, bool) {
	store := iss.accountStore()
	store.mu.RLock()
	account, ok := store.accounts[key]
	store.mu.RUnlock()
	return account, ok
}

func (iss *ACMEIssuer) cacheAccount(key acmeAccountCacheKey, account acme.Account) {
	// Never publish an unregistered account: its private key is not a
	// durable identity and sharing it would make concurrent requests race
	// to register different keys under the same account.
	if account.Status == "" {
		return
	}
	store := iss.accountStore()
	store.mu.Lock()
	store.accounts[key] = account
	store.mu.Unlock()
}

// cacheLoadedAccount publishes an account read from storage only if a newer
// value (for example, one just registered and saved by another goroutine) is
// not already cached. This prevents a slow reader that started before a
// registration from restoring the superseded account afterwards.
func (iss *ACMEIssuer) cacheLoadedAccount(key acmeAccountCacheKey, account acme.Account) {
	if account.Status == "" {
		return
	}
	iss.cachePersistedAccount(key, account)
}

// cachePersistedAccount publishes an account that came from durable storage.
// Unlike cacheAccount, it does not require a non-empty status, because the
// presence of the account files is itself sufficient evidence that the key
// belongs to a durable account.
func (iss *ACMEIssuer) cachePersistedAccount(key acmeAccountCacheKey, account acme.Account) {
	store := iss.accountStore()
	store.mu.Lock()
	if _, ok := store.accounts[key]; !ok {
		store.accounts[key] = account
	}
	store.mu.Unlock()
}

func (iss *ACMEIssuer) invalidateAccountCache(string) {
	store := iss.accountStore()
	store.mu.Lock()
	for key := range store.accounts {
		// Invalidate every account in this issuer's store. Account
		// recreation is rare, and being conservative here avoids retaining
		// an account that no longer exists after recreation or a CA change.
		delete(store.accounts, key)
	}
	store.mu.Unlock()
}

// When an email address is not explicitly specified, we can remember
// the last one we discovered to avoid having to ask again later.
// (We used to store this in DefaultACME.Email but it was racey; see #127)
var (
	discoveredEmail   string
	discoveredEmailMu sync.Mutex
)

// stdin is used to read the user's input if prompted;
// this is changed by tests during tests.
var stdin = io.ReadWriter(os.Stdin)

// The name of the folder for accounts where the email
// address was not provided; default 'username' if you will,
// but only for local/storage use, not with the CA.
const emptyEmail = "default"

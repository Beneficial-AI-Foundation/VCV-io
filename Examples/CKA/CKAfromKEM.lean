import Examples.CKA.Defs
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# CKA from KEM

Generic construction of a CKA scheme from a KEM, following [ACD19, Section 4.1].
https://eprint.iacr.org/2018/1037.pdf

## Construction

Given a KEM with key space `K`, public/secret keys `PK`/`SK`, and ciphertexts `C`:

- Initial key space `IK = PK × SK` — a KEM key pair.
- Epoch key space `I = K` — KEM shared keys.
- Message space `Rho = C × PK` — a ciphertext and a fresh public key.
- State space `St = PK ⊕ SK`:
  `.inl pk` (public key, after init or recv) or `.inr sk` (secret key, after send).

## Main Definitions

- `kemCKA` — CKA construction from KEM.
-/

open OracleSpec OracleComp ENNReal

variable {K PK SK C : Type}

/-- Wrapper for using a probabilistic KEM with the pure-receive CKA interface:
decapsulation must in fact be extensionally deterministic. -/
class DeterministicDecaps (kem : KEMScheme ProbComp K PK SK C) where
  decapsFn : SK → C → Option K
  decaps_spec : ∀ sk c, kem.decaps sk c = pure (decapsFn sk c)

/-- send(pk): (c, key) ← encaps(pk); (pk', sk') ← keygen;
return (key, (c, pk'), sk') -/
def kemCKA.send (kem : KEMScheme ProbComp K PK SK C) (st : PK ⊕ SK) :
    ProbComp (K × (C × PK) × (PK ⊕ SK)) :=
  match st with
  | .inl pk => do
    let (c, key) ← kem.encaps pk
    let (pk', sk') ← kem.keygen
    return (key, (c, pk'), .inr sk')
  | .inr _ => do
    let (pk', sk') ← kem.keygen
    let (c, key) ← kem.encaps pk'
    return (key, (c, pk'), .inr sk')

/-- recv(sk, (c, pk')): key ← decaps(sk, c); return (key, pk') -/
def kemCKA.recv [Inhabited K] (kem : KEMScheme ProbComp K PK SK C)
    [DeterministicDecaps kem] (st : PK ⊕ SK) (msg : C × PK) : Option K × (PK ⊕ SK) :=
  match st with
  | .inr sk =>
    let (c, pk') := msg
    (DeterministicDecaps.decapsFn (kem := kem) sk c, .inl pk')
  | .inl _ =>
    let (_, pk') := msg
    (some default, .inl pk')

/-- CKA from KEM [ACD19, Section 4.1].

- `initKeyGen`: `(pk, sk) ← KEM.keygen`
- `initA(pk, sk)`: store `pk`; `initB(pk, sk)`: store `sk`
- `send(pk)`: encapsulate under `pk`, generate fresh key pair, send `(c, pk')`
- `recv(sk, (c, pk'))`: decapsulate `c` with `sk`, store `pk'`

Send and recv are the same for both parties; only init differs. -/
def kemCKA [Inhabited K] (kem : KEMScheme ProbComp K PK SK C) [DeterministicDecaps kem] :
    CKAScheme ProbComp
    (IK := PK × SK) (St := PK ⊕ SK) (I := K) (Rho := C × PK) where
  initKeyGen := kem.keygen
  initA := fun (pk, _) => return .inl pk
  initB := fun (_, sk) => return .inr sk
  sendA := kemCKA.send kem
  sendB := kemCKA.send kem
  recvA := kemCKA.recv kem
  recvB := kemCKA.recv kem
  __ := ExecutionMethod.default

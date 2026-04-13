import Examples.CKA.Defs
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# CKA from DDH — Construction

Construction of a CKA scheme from the DDH assumption over a module `Module F G`,
following [ACD19, Section 4.1].
https://eprint.iacr.org/2018/1037.pdf

## Construction
We consider a module `Module F G` with scalar field `F`, additive group `G`,
scalar multiplication `a • gen`, and a fixed generator `gen : G`.

- Initial key space `IK = G × F` — a group element and its discrete log.
- Epoch key space `I = G` — DH shared secrets.
- Message space `Rho = G` — DH public values.
- State space `St = F ⊕ G` — holds :
  A scalar in F after a Send action, or else group element in G after a receive action.
-/

open OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- send(h): x ←$ F; key := x • h, ρ := x • gen, state := x -/
def ddhCKA.send (gen : G) (st : F ⊕ G) : ProbComp (G × G × (F ⊕ G)) :=
  match st with
  | .inr h => do let x ← $ᵗ F; return (x • h, x • gen, .inl x)
  | .inl _ => return (0, 0, .inl 0)

/-- recv(x, ρ): key := x • ρ, state := ρ -/
def ddhCKA.recv (st : F ⊕ G) (ρ : G) : Option G × (F ⊕ G) :=
  match st with
  | .inl x => (some (x • ρ), .inr ρ)
  | .inr _ => (some ρ, .inr ρ)

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
/-- `recv(y, x • g) = (some (x • (y • g)), x • g)` by `smul_comm`. -/
theorem ddhCKA.recv_key_agree (x y : F) (gen : G) :
    ddhCKA.recv (.inl y) (x • gen) = (some (x • (y • gen)), .inr (x • gen)) := by
  simp [ddhCKA.recv, smul_comm y x gen]

/-- CKA from DDH over a module `Module F G` with generator `gen : G`.

- `initKeyGen`: x₀ ←$ F; return (x₀ • gen, x₀)
- `initA(h, x₀)`: store h ∈ G; `initB(h, x₀)`: store x₀ ∈ F
- send and recv are the same for both parties; only init differs. -/
def ddhCKA (F G : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : CKAScheme ProbComp
    (IK := G × F) (St := F ⊕ G) (I := G) (Rho := G) where
  initKeyGen := do
    let x ← $ᵗ F
    return (x • gen, x)
  initA := fun (h, _) => return .inr h
  initB := fun (_, x) => return .inl x
  sendA := ddhCKA.send gen
  sendB := ddhCKA.send gen
  recvA := ddhCKA.recv
  recvB := ddhCKA.recv

import Examples.CKA.Defs
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# CKA from DDH

Construction of a CKA scheme from the DDH assumption over a module `Module F G`,
following [ACD19, Section 4.1].
https://eprint.iacr.org/2018/1037.pdf

## Construction
We work over a module `Module F G` with scalar field `F`, additive group `G`,
scalar multiplication `a • gen`, and a fixed generator `gen : G`.

- Initial key space `IK = G × F` — a group element and its discrete log.
- Epoch key space `I = G` — DH shared secrets.
- Message space `Rho = G` — DH public values.
- State space `St = F ⊕ G` — holds exactly one element at a time:
  `.inr h` (group element, after init or recv) or `.inl x` (scalar, after send).
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
- Send and recv are the same for both parties; only init differs. -/
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
  __ := ExecutionMethod.default

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme

/-! ### Game invariant -/

/-- Four-phase game-state invariant for DDH-CKA correctness.

The game state `(stA, stB, ρA, ρB, kA, kB)` cycles through four phases:
- **Sync-A** (initial / after `recvA`): `(x•g, x, -, -, -, -)`.
- **Pending-A→B** (after `sendA`): `(y, x, y•g, -, y•(x•g), -)`.
- **Sync-B** (after `recvB`): `(y, y•g, -, -, -, -)`.
- **Pending-B→A** (after `sendB`): `(y, x', -, x'•g, -, x'•(y•g))`. -/
private def gameInv (gen : G) (state : GameState (F ⊕ G) G G) : Prop :=
  let ⟨sA, sB, ρA, ρB, kA, kB, _, correct, last⟩ := state
  correct = true ∧
  match last with
  | none | some .recvA =>
    ∃ x : F, sA = .inr (x • gen) ∧ sB = .inl x ∧
      ρA = none ∧ ρB = none ∧ kA = none ∧ kB = none
  | some .sendA =>
    ∃ x y : F, sA = .inl y ∧ sB = .inl x ∧
      ρA = some (y • gen) ∧ ρB = none ∧
      kA = some (y • (x • gen)) ∧ kB = none
  | some .recvB =>
    ∃ y : F, sA = .inl y ∧ sB = .inr (y • gen) ∧
      ρA = none ∧ ρB = none ∧ kA = none ∧ kB = none
  | some .sendB =>
    ∃ x y : F, sA = .inl y ∧ sB = .inl x ∧
      ρA = none ∧ ρB = some (x • gen) ∧
      kA = none ∧ kB = some (x • (y • gen))
  | some .challA | some .challB => False

/-- `gameInv` holds on `initGameState` for any key `(x₀ • gen, x₀)`. -/
private lemma gameInv_init (x₀ : F) :
    gameInv gen (initGameState (.inr (x₀ • gen)) (.inl x₀) false) :=
  ⟨rfl, x₀, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Correctness theorem -/

/-- The correctness game never fails (all sampling is total). -/
private lemma nofail [DecidableEq G] (adv : CorrectnessAdversary G G) :
    Pr[⊥ | correctnessExp (ddhCKA F G gen) adv] = 0 := by
  sorry

/-- The correctness game always outputs `true`: `gameInv` is established by
`gameInv_init`, preserved by every oracle call (via `recv_key_agree`), and
implies `correct = true` on every reachable final state. -/
private lemma always_correct [DecidableEq G] (adv : CorrectnessAdversary G G)
    (b : Bool) (hb : b ∈ support (correctnessExp (ddhCKA F G gen) adv)) :
    b = true := by
  sorry

/-- DDH-CKA correctness. -/
theorem correctness [DecidableEq G] (adv : CorrectnessAdversary G G) :
    Pr[= true | correctnessExp (ddhCKA F G gen) adv] = 1 := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  exact ⟨nofail adv, always_correct adv⟩

end ddhCKA

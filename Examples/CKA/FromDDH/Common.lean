import Examples.CKA.FromDDH.Construction

/-!
# CKA from DDH — Common Results

Shared reachable-state invariants for the DDH-based CKA example.
-/

open OracleSpec OracleComp ENNReal
open CKAScheme

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

namespace ddhCKA

/-- Reachable security/correctness states obey the communication-phase counter relation. -/
def phaseCounterInv (s : GameState (F ⊕ G) G G) : Prop :=
  match s.lastAction with
  | none | some .recvA | some .recvB => s.tA = s.tB
  | some .sendA | some .challA => s.tA = s.tB + 1
  | some .sendB | some .challB => s.tB = s.tA + 1

/-- Honest DDH-CKA states have one of the four expected protocol shapes keyed by
`lastAction`. -/
def phaseShapeInv (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  match s.lastAction with
  | none | some .recvA =>
    ∃ x : F, s.stA = .inr (x • gen) ∧ s.stB = .inl x ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none
  | some .sendA | some .challA =>
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.lastRhoA = some (y • gen) ∧ s.lastRhoB = none ∧
      s.lastKeyA = some (y • (x • gen)) ∧ s.lastKeyB = none
  | some .recvB =>
    ∃ y : F, s.stA = .inl y ∧ s.stB = .inr (y • gen) ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none
  | some .sendB | some .challB =>
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.lastRhoA = none ∧ s.lastRhoB = some (x • gen) ∧
      s.lastKeyA = none ∧ s.lastKeyB = some (x • (y • gen))

/-- Shared reachable-state invariant for the DDH-CKA construction. -/
def reachableInv (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  phaseCounterInv s ∧
  s.correct = true ∧
  phaseShapeInv gen s

end ddhCKA

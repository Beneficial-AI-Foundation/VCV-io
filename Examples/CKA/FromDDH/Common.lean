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
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendA | some .challA =>
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.rhoA = some (y • gen) ∧ s.rhoB = none ∧
      s.keyA = some (y • (x • gen)) ∧ s.keyB = none
  | some .recvB =>
    ∃ y : F, s.stA = .inl y ∧ s.stB = .inr (y • gen) ∧
      s.rhoA = none ∧ s.rhoB = none ∧ s.keyA = none ∧ s.keyB = none
  | some .sendB | some .challB =>
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.rhoA = none ∧ s.rhoB = some (x • gen) ∧
      s.keyA = none ∧ s.keyB = some (x • (y • gen))

/-- Structural (correctness-independent) invariant: phase counter plus phase shape.
Suitable for relations that normalize `correct` (e.g. `hybridProj`). -/
def reachableShape (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  phaseCounterInv s ∧ phaseShapeInv gen s

/-- Shared reachable-state invariant for the DDH-CKA construction. -/
def reachableInv (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  phaseCounterInv s ∧
  s.correct = true ∧
  phaseShapeInv gen s

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
lemma reachableShape_of_reachableInv {gen : G} {s : GameState (F ⊕ G) G G}
    (h : reachableInv gen s) : reachableShape gen s :=
  ⟨h.1, h.2.2⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
lemma correct_of_reachableInv {gen : G} {s : GameState (F ⊕ G) G G}
    (h : reachableInv gen s) : s.correct = true :=
  h.2.1

end ddhCKA

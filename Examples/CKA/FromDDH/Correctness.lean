import Examples.CKA.FromDDH.Construction

/-!
# CKA from DDH — Correctness

Correctness proof for the DDH-CKA construction: `Pr[= true | correctnessExp] = 1`.
The proof establishes a four-phase game invariant and shows it is preserved by
every oracle call, using `smul_comm` for key agreement.
-/

open OracleSpec OracleComp ENNReal

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme

/-- Game invariant for DDH-CKA correctness.

Asserts `correct = true` and one of four phases for the game state
`state = (stA, stB, ρA, ρB, kA, kB, b, correct, lastAction)`:

- **Sync-A**: `(x•g, x, -, -, -, -, b, true, none/recvA)`.
- **Pending-A→B**: `(y, x, y•g, -, y•(x•g), -, b, true, sendA/challA)`.
- **Sync-B**: `(y, y•g, -, -, -, -, b, true, recvB)`.
- **Pending-B→A**: `(y, x', -, x'•g, -, x'•(y•g), b, true, sendB/challB)`. -/
private def gameInvariant (gen : G) (s : GameState (F ⊕ G) G G) : Prop :=
  s.correct = true ∧
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

/-! ### Invariant preservation -/

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
/-- `gameInvariant` holds on `initGameState` for any key `(x₀ • gen, x₀)`. -/
private lemma gameInvariant_init (x₀ : F) :
    gameInvariant gen
      { stA := .inr (x₀ • gen), stB := .inl x₀,
        lastRhoA := none, lastRhoB := none, lastKeyA := none, lastKeyB := none,
        b := false, correct := true, lastAction := none,
        tA := 0, tB := 0, params := ⟨0, 0, .A⟩ } :=
  ⟨rfl, x₀, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G] in
/-- Uniform sampling preserves `gameInvariant` (state unchanged). -/
private lemma oracleUnif_preserves_gameInvariant :
    QueryImpl.PreservesInv (CKAScheme.oracleUnif (F ⊕ G) G G) (gameInvariant gen) := by
  intro t σ hσ z hz
  have hz' : ∃ y : unifSpec.Range t, (y, σ) = z := by
    simpa [CKAScheme.oracleUnif] using hz
  rcases hz' with ⟨_, rfl⟩
  simpa using hσ

set_option linter.flexible false in
/-- `O-Send-A` preserves `gameInvariant`:
`(x•g, x, -, -, -, -)` → sample `y` → `(y, x, y•g, -, y•(x•g), -)`. -/
private lemma oracleSendA_preserves_gameInvariant :
    QueryImpl.PreservesInv (CKAScheme.oracleSendA (ddhCKA F G gen)) (gameInvariant gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩
  cases hGuard : validStep last .sendA
  case false =>
    have : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩) := by
      simpa [CKAScheme.oracleSendA, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals (
      rcases (by simpa [gameInvariant] using hσ) with ⟨hc, x, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      rw [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
      have hz' := hz; simp [validStep, ddhCKA, ddhCKA.send] at hz'
      obtain ⟨y, _, rfl⟩ := hz'
      exact ⟨rfl, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `O-Recv-B` preserves `gameInvariant`:
`(y, x, y•g, -, y•(x•g), -)` → `(y, y•g, -, -, -, -)`;
key check: `x•(y•g) = y•(x•g)` by `smul_comm`. -/
private lemma oracleRecvB_preserves_gameInvariant [DecidableEq G] :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvB (ddhCKA F G gen)) (gameInvariant gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩
  cases hGuard : validStep last .recvB
  case false =>
    have : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩) := by
      simpa [CKAScheme.oracleRecvB, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals (
      rcases (by simpa [gameInvariant] using hσ) with ⟨hc, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      have : z = ((), ⟨.inl y, .inr (y • gen),
          none, none, none, none, b, true,
          some .recvB, epA, epB + 1, gp⟩) := by
        simpa [CKAScheme.oracleRecvB, validStep,
          ddhCKA, ddhCKA.recv, smul_comm x y gen,
          StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst this
      exact ⟨rfl, y, rfl, rfl, rfl, rfl, rfl, rfl⟩)

set_option linter.flexible false in
/-- `O-Send-B` preserves `gameInvariant`:
`(y, y•g, -, -, -, -)` → sample `x'` → `(y, x', -, x'•g, -, x'•(y•g))`. -/
private lemma oracleSendB_preserves_gameInvariant :
    QueryImpl.PreservesInv (CKAScheme.oracleSendB (ddhCKA F G gen)) (gameInvariant gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩
  cases hGuard : validStep last .sendB
  case false =>
    have : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩) := by
      simpa [CKAScheme.oracleSendB, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    rcases (by simpa [gameInvariant] using hσ) with ⟨hc, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
    subst correct
    rw [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    have hz' := hz; simp [validStep, ddhCKA, ddhCKA.send] at hz'
    obtain ⟨x, _, rfl⟩ := hz'
    exact ⟨rfl, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `O-Recv-A` preserves `gameInvariant`:
`(y, x', -, x'•g, -, x'•(y•g))` → `(x'•g, x', -, -, -, -)`;
key check: `y•(x'•g) = x'•(y•g)` by `smul_comm`. -/
private lemma oracleRecvA_preserves_gameInvariant [DecidableEq G] :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvA (ddhCKA F G gen)) (gameInvariant gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩
  cases hGuard : validStep last .recvA
  case false =>
    have : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, gp⟩) := by
      simpa [CKAScheme.oracleRecvA, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true =>
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals (
      rcases (by simpa [gameInvariant] using hσ) with ⟨hc, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      have : z = ((), ⟨.inr (x • gen), .inl x,
          none, none, none, none, b, true,
          some .recvA, epA + 1, epB, gp⟩) := by
        simpa [CKAScheme.oracleRecvA, validStep,
          ddhCKA, ddhCKA.recv, smul_comm y x gen,
          StateT.run_bind, StateT.run_get,
          pure_bind] using hz
      subst this
      exact ⟨rfl, x, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- The combined correctness oracle preserves `gameInvariant`. -/
private lemma correctnessImpl_preserves [DecidableEq G] :
    QueryImpl.PreservesInv
      (CKAScheme.ckaCorrectnessImpl (ddhCKA F G gen))
      (gameInvariant gen) := by
  intro t σ hσ z hz
  cases t with
  | inl t =>
      cases t with
      | inl t =>
          cases t with
          | inl t =>
              cases t with
              | inl t =>
                  simpa [CKAScheme.ckaCorrectnessImpl] using
                    oracleUnif_preserves_gameInvariant (gen := gen) t σ hσ z hz
              | inr _ =>
                  simpa [CKAScheme.ckaCorrectnessImpl] using
                    oracleSendA_preserves_gameInvariant (gen := gen) () σ hσ z hz
          | inr _ =>
              simpa [CKAScheme.ckaCorrectnessImpl] using
                oracleRecvA_preserves_gameInvariant (gen := gen) () σ hσ z hz
      | inr _ =>
          simpa [CKAScheme.ckaCorrectnessImpl] using
            oracleSendB_preserves_gameInvariant (gen := gen) () σ hσ z hz
  | inr _ =>
      simpa [CKAScheme.ckaCorrectnessImpl] using
        oracleRecvB_preserves_gameInvariant (gen := gen) () σ hσ z hz

/-! ### Correctness theorem -/

private lemma nofail [DecidableEq G] (adv : CorrectnessAdversary G G) :
    Pr[⊥ | correctnessExp (ddhCKA F G gen) adv] = 0 := by
  exact probFailure_eq_zero

private lemma always_correct [DecidableEq G] (adv : CorrectnessAdversary G G)
    (b : Bool) (hb : b ∈ support (correctnessExp (ddhCKA F G gen) adv)) :
    b = true := by
  unfold CKAScheme.correctnessExp at hb
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨ik, hik, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stA, hstA, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨stB, hstB, hb⟩
  rw [mem_support_bind_iff] at hb
  rcases hb with ⟨out, hout, hb⟩
  have hik' : ∃ x₀ : F, ik = (x₀ • gen, x₀) := by
    rcases (by simpa [ddhCKA, mem_support_bind_iff, mem_support_pure_iff] using hik :
      ∃ x₀ : F, (x₀ • gen, x₀) = ik) with ⟨x₀, hx₀⟩
    exact ⟨x₀, hx₀.symm⟩
  rcases hik' with ⟨x₀, rfl⟩
  have hstA' : stA = .inr (x₀ • gen) := by
    simpa [ddhCKA, mem_support_pure_iff] using hstA
  have hstB' : stB = .inl x₀ := by
    simpa [ddhCKA, mem_support_pure_iff] using hstB
  subst stA
  subst stB
  have hInv :
      gameInvariant gen out.2 := by
    exact OracleComp.simulateQ_run_preservesInv
      (impl := CKAScheme.ckaCorrectnessImpl (ddhCKA F G gen))
      (Inv := gameInvariant gen)
      (correctnessImpl_preserves (F := F) (G := G) (gen := gen))
      adv
      { stA := .inr (x₀ • gen), stB := .inl x₀,
        lastRhoA := none, lastRhoB := none,
        lastKeyA := none, lastKeyB := none,
        b := false, correct := true, lastAction := none,
        tA := 0, tB := 0, params := ⟨0, 0, .A⟩ }
      (gameInvariant_init (gen := gen) x₀)
      out
      hout
  have hb' : b = out.2.correct := by
    simpa [mem_support_pure_iff] using hb
  exact hb'.trans hInv.1

/-- DDH-CKA correctness: `Pr[= true | correctnessExp] = 1`. -/
theorem correctness [DecidableEq G] (adv : CorrectnessAdversary G G) :
    Pr[= true | correctnessExp (ddhCKA F G gen) adv] = 1 := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  exact ⟨nofail adv, always_correct adv⟩

end ddhCKA

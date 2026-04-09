import Examples.CKA.Defs
import ToMathlib.Control.StateT
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# CKA from DDH

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

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme

/-! ### Correctness proof -/

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
  | none | some .recvA => -- initial state or state after O-Recv-A
    ∃ x : F, s.stA = .inr (x • gen) ∧ s.stB = .inl x ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none
  | some .sendA | some .challA => -- state after O-Send-A or O-Chall-A
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.lastRhoA = some (y • gen) ∧ s.lastRhoB = none ∧
      s.lastKeyA = some (y • (x • gen)) ∧ s.lastKeyB = none
  | some .recvB => -- state after O-Recv-B
    ∃ y : F, s.stA = .inl y ∧ s.stB = .inr (y • gen) ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none
  | some .sendB | some .challB => -- state after O-Send-B or O-Chall-B
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
        tA := 0, tB := 0, tStar := 0, deltaCKA := 0 } :=
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
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩
  cases hGuard : validStep last .sendA
  case false => -- guard failed → no-op
    have : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩) := by
      simpa [CKAScheme.oracleSendA, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true => -- guard passed → sync-A phase (last = none | recvA)
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals (
      rcases (by simpa [gameInvariant] using hσ) with ⟨hc, x, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      rw [CKAScheme.oracleSendA, StateT.run_bind, StateT.run_get] at hz
      have hz' := hz; simp [validStep] at hz'
      obtain ⟨key, ρ, ⟨y, hu, rfl⟩ | ⟨_, hu, _⟩⟩ := hz'
      · rcases (by simpa [ddhCKA, ddhCKA.send] using hu) with ⟨rfl, rfl⟩
        exact ⟨rfl, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact absurd hu (by simp [ddhCKA, ddhCKA.send]))

/-- `O-Recv-B` preserves `gameInvariant`:
`(y, x, y•g, -, y•(x•g), -)` → `(y, y•g, -, -, -, -)`;
key check: `x•(y•g) = y•(x•g)` by `smul_comm`. -/
private lemma oracleRecvB_preserves_gameInvariant [DecidableEq G] :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvB (ddhCKA F G gen)) (gameInvariant gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩
  cases hGuard : validStep last .recvB
  case false => -- guard failed → no-op
    have : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩) := by
      simpa [CKAScheme.oracleRecvB, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true => -- guard passed → pending-A→B phase (last = sendA | challA)
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals (
      rcases (by simpa [gameInvariant] using hσ) with ⟨hc, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      have : z = ((),
        ⟨.inl y, .inr (y • gen), none, none, none, none, b, true, some .recvB, epA, epB, ts, dc⟩) := by
        simpa [CKAScheme.oracleRecvB, validStep, ddhCKA, ddhCKA.recv, smul_comm x y gen,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst this
      exact ⟨rfl, y, rfl, rfl, rfl, rfl, rfl, rfl⟩)

set_option linter.flexible false in
/-- `O-Send-B` preserves `gameInvariant`:
`(y, y•g, -, -, -, -)` → sample `x'` → `(y, x', -, x'•g, -, x'•(y•g))`. -/
private lemma oracleSendB_preserves_gameInvariant :
    QueryImpl.PreservesInv (CKAScheme.oracleSendB (ddhCKA F G gen)) (gameInvariant gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩
  cases hGuard : validStep last .sendB
  case false => -- guard failed → no-op
    have : z = (none, ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩) := by
      simpa [CKAScheme.oracleSendB, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true => -- guard passed → sync-B phase (last = recvB)
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    rcases (by simpa [gameInvariant] using hσ) with ⟨hc, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
    subst correct
    rw [CKAScheme.oracleSendB, StateT.run_bind, StateT.run_get] at hz
    have hz' := hz; simp [validStep] at hz'
    obtain ⟨key, ρ, ⟨x, hu, rfl⟩ | ⟨_, hu, _⟩⟩ := hz'
    · rcases (by simpa [ddhCKA, ddhCKA.send] using hu) with ⟨rfl, rfl⟩
      exact ⟨rfl, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd hu (by simp [ddhCKA, ddhCKA.send])

/-- `O-Recv-A` preserves `gameInvariant`:
`(y, x', -, x'•g, -, x'•(y•g))` → `(x'•g, x', -, -, -, -)`;
key check: `y•(x'•g) = x'•(y•g)` by `smul_comm`. -/
private lemma oracleRecvA_preserves_gameInvariant [DecidableEq G] :
    QueryImpl.PreservesInv (CKAScheme.oracleRecvA (ddhCKA F G gen)) (gameInvariant gen) := by
  intro _ σ hσ z hz
  rcases σ with ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩
  cases hGuard : validStep last .recvA
  case false => -- guard failed → no-op
    have : z = ((), ⟨sA, sB, ρA, ρB, kA, kB, b, correct, last, epA, epB, ts, dc⟩) := by
      simpa [CKAScheme.oracleRecvA, hGuard, StateT.run_bind, StateT.run_get, pure_bind] using hz
    subst this; exact hσ
  case true => -- guard passed → pending-B→A phase (last = sendB | challB)
    rcases last with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> simp [validStep] at hGuard
    all_goals (
      rcases (by simpa [gameInvariant] using hσ) with ⟨hc, x, y, rfl, rfl, rfl, rfl, rfl, rfl⟩
      subst correct
      have : z = ((),
        ⟨.inr (x • gen), .inl x, none, none, none, none, b, true, some .recvA, epA, epB, ts, dc⟩) := by
        simpa [CKAScheme.oracleRecvA, validStep, ddhCKA, ddhCKA.recv, smul_comm y x gen,
          StateT.run_bind, StateT.run_get, pure_bind] using hz
      subst this
      exact ⟨rfl, x, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- The combined correctness oracle (send + recv for both parties) preserves `gameInvariant` -/
private lemma correctnessImpl_preserves_gameInvariant [DecidableEq G] :
    QueryImpl.PreservesInv (CKAScheme.ckaCorrectnessImpl (ddhCKA F G gen)) (gameInvariant gen) := by
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

/-- The correctness game never fails (all sampling is total). -/
private lemma nofail [DecidableEq G] (adv : CorrectnessAdversary G G) :
    Pr[⊥ | correctnessExp (ddhCKA F G gen) adv] = 0 := by
  exact probFailure_eq_zero

/-- The correctness game always outputs `true`: `gameInvariant` is established by
`gameInvariant_init`, preserved by every oracle call (via `recv_key_agree`), and
implies `correct = true` on every reachable final state. -/
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
      (correctnessImpl_preserves_gameInvariant (F := F) (G := G) (gen := gen))
      adv
      { stA := .inr (x₀ • gen), stB := .inl x₀,
        lastRhoA := none, lastRhoB := none, lastKeyA := none, lastKeyB := none,
        b := false, correct := true, lastAction := none,
        tA := 0, tB := 0, tStar := 0, deltaCKA := 0 }
      (gameInvariant_init (gen := gen) x₀)
      out
      hout
  have hb' : b = out.2.correct := by
    simpa [mem_support_pure_iff] using hb
  exact hb'.trans hInv.1

/-- DDH-CKA correctness. -/
theorem correctness [DecidableEq G] (adv : CorrectnessAdversary G G) :
    Pr[= true | correctnessExp (ddhCKA F G gen) adv] = 1 := by
  rw [← probEvent_eq_eq_probOutput, probEvent_eq_one_iff]
  exact ⟨nofail adv, always_correct adv⟩

end ddhCKA

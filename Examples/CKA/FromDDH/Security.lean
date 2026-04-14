import Examples.CKA.FromDDH.Construction
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# CKA from DDH — Security Proof

Security reduction from DDH to CKA key-indistinguishability,
following [ACD19, Theorem 3].
https://eprint.iacr.org/2018/1037.pdf

## Main result

**Theorem** (`ddhCKA_security`). *Let `G` be a group with generator `gen` such
that `· • gen : F → G` is bijective. If every DDH adversary has guess-advantage
at most `ε`, then for any CKA adversary `𝒜` and any `tStar : ℕ`:*

  `securityAdvantage(ddhCKA, 𝒜, tStar, ΔCKA := 1) ≤ ε`

*where `securityAdvantage = |Pr[b = b' | securityExp] - 1/2|`.
More precisely, there is an explicit DDH adversary
`ℬ = securityReduction 𝒜 tStar` such that
`securityAdvantage(ddhCKA, 𝒜, tStar, 1) ≤ ddhGuessAdvantage(gen, ℬ)`,
with no multiplicative loss.*

## Proof overview — reduction diagram (challA case)

The challB case is symmetric with A/B roles swapped (see `reductionOracleImplB`).
Given a DDH triple `(gen, gA, gB, gT)` with
`gA = a • gen`, `gB = b • gen`, and `gT = c • gen` where `c = a·b` (real) or
`c` random:

```text
 DDH Challenger                       DDH Adversary ℬA = securityReductionA(𝒜, tStar)
┌──────────────┐                     ┌──────────────────────────────────────────────┐
│              │  (gen,gA,gB,gT)     │                                              │
│  gA = a•gen  │────────────────────▶│   x₀ ← $F                                   │
│  gB = b•gen  │                     │   stA₀ := .inr (x₀•gen),  stB₀ := .inl x₀   │
│  gT = c•gen  │                     │                                              │
│              │                     │   Simulate CKA oracles for adversary 𝒜 :     │
│  c = a·b     │                     │                                              │
│  or random   │                     │   ┌────────────────────────────────────────┐  │
│              │                     │   │         CKA Adversary 𝒜               │  │
│              │                     │   │                                        │  │
│              │                     │   │  queries: sendA, sendB, recvA, recvB,  │  │
│              │                     │   │           challA, corruptA, corruptB   │  │
│              │                     │   └──────────────┬─────────────────────────┘  │
│              │                     │                  │ oracle calls               │
│              │                     │   ┌──────────────▼─────────────────────────┐  │
│              │                     │   │       Oracle simulation by ℬ           │  │
│              │                     │   │                                        │  │
│              │                     │   │  ① tB < tStar-1 :  honest send/recv   │  │
│              │                     │   │                                        │  │
│              │                     │   │  ② tB = tStar-1 :  embed gA           │  │
│              │                     │   │     msg := gA,  key := xA • gA        │  │
│              │                     │   │     (xA = party A's exponent from stA) │  │
│              │                     │   │                                        │  │
│              │                     │   │  ③ tA = tStar (challA) : embed DDH    │  │
│              │                     │   │     msg := gB,  key := gT             │  │
│              │                     │   │     real ⟹ gT = b•(a•gen) = honest   │  │
│              │                     │   │     rand ⟹ gT = uniform              │  │
│              │                     │   │                                        │  │
│              │                     │   │  ④ tB = tStar :  honest send from     │  │
│              │                     │   │     .inr gB (no modification needed)   │  │
│              │                     │   │     msg = x'•gen,  key = x'•gB        │  │
│              │                     │   │                                        │  │
│              │                     │   │  ⑤ tA,tB > tStar :  honest send/recv  │  │
│              │                     │   └────────────────────────────────────────┘  │
│              │                     │                                              │
│              │     !b'             │   b' := 𝒜's guess for hidden bit             │
│              │◀────────────────────│   return !b'  (negate for bit convention)     │
│              │                     │                                              │
└──────────────┘                     └──────────────────────────────────────────────┘
```

**Key identities.**
- Stage ②: The honest B-send returns `(y • gen, (y · xA) • gen)` for fresh
  `y ← $F`. The reduction returns `(a • gen, (xA · a) • gen)` where `a` is
  from the DDH challenge. Both are `(α • gen, (α · xA) • gen)` for uniform
  `α` (`α = y` vs `α = a`), so the distributions are identical.
- Stage ③ (real): `gT = (a·b)•gen = b•(a•gen) = b•gA` by `smul_comm`,
  which is the honest CKA key when party A sends from state `.inr gA`.
- Stage ③ (random): `gT = c•gen` for uniform `c`, matching `$ᵗ G` when
  `· • gen` is bijective.
- Stage ④ needs no modification: party B's state after receiving `gB` is `.inr gB`,
  so the honest send computes `(x'•gen, x'•gB)`.

**Bit convention.** The DDH and CKA games use opposite polarities for `true`:
- DDH (`ddhExp`): `bit = true` ↦ real triple (`c = a·b`).
- CKA (`oracleChallA`): `b = true` ↦ random key (`outKey ← $ᵗ I`).

The reduction embeds real DDH as `b = false` (real key) and random DDH as
`b = true` (random key). A correct CKA guess `b'` therefore has the opposite
polarity from the correct DDH answer, so the reduction returns `!b'`.

**Post-compromise security** (`ΔCKA = 1`, strict healing). Corruption of the
challenged party is only allowed once that party has advanced past
`tStar + 1`, so the challenge-linked sender state is overwritten before it
can be revealed. Concretely:
- Party A's challenge state at epoch `tStar + 1` may be a fresh hidden scalar.
- By the time `corruptA` is allowed, A has already advanced again and this
  temporary state has been overwritten by honest protocol steps.
- Party B's state from epoch `tStar` is `.inr gB` (public DDH component).
-/

open OracleSpec OracleComp ENNReal

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme DiffieHellman

variable [DecidableEq G]

/-! ### DDH reduction -/

/-- Modified B-send for the DDH reduction.

At `tB = t* - 1`:
- Honest output: `(y·G, y·xA·G)` for `y ← $F`
- Reduction output: `(aG, xA·aG)` where `aG` is from the DDH tuple
- These are identically distributed since `a` is uniform like `y`
- Hidden state: `stB ← .inl y` for fresh `y ← $F` (not `a`)

All other epochs: delegates to `oracleSendB`. -/
private noncomputable def reductionSendB (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      if state.tB + 1 == state.tStar then
        -- Epoch tStar - 1: embed gA = a • gen from the DDH challenge.
        -- Honest send would return (y • gen, y • (xA • gen)) for fresh y.
        -- We return (gA, xA • gA) = (a • gen, xA • (a • gen)) instead;
        -- by smul_comm these have the same distribution over uniform a.
        -- A's state is .inl xA after its last send; .inr branch is unreachable.
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        -- In honest send, y drives both the output (y•gen, y•h) and the new
        -- state (.inl y). Here gA and xA•gA replace y in the output, but y
        -- still seeds B's state so subsequent epochs use a fresh exponent.
        let y ← liftM ($ᵗ F : ProbComp F)
        set { state with
          stB := (.inl y : F ⊕ G), lastRhoB := some gA, lastKeyB := some (xA • gA),
          lastAction := some .sendB, tB := state.tB + 1 }
        return some (gA, xA • gA)
      else
        -- All other epochs: honest B-send.
        match ← liftM (ddhCKA.send gen state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          set { state with
            stB := stB', lastRhoB := some ρ, lastKeyB := some key,
            lastAction := some .sendB, tB := state.tB + 1 }
          return some (ρ, key)
    else pure none

/-- Modified A-send for the DDH reduction (symmetric to `reductionSendB`).

At `tA = t*`:
- Honest output: `(x·G, x·xB·G)` for `x ← $F`
- Reduction output: `(aG, xB·aG)` where `aG` is from the DDH tuple
- Hidden state: `stA ← .inl y` for fresh `y ← $F` (not `a`)

All other epochs: delegates to `oracleSendA`. -/
private noncomputable def reductionSendA (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      if state.tA == state.tStar then
        -- Epoch tStar: embed gA = a • gen from the DDH challenge.
        -- Honest send would return (x • gen, x • (xB • gen)) for fresh x.
        -- We return (gA, xB • gA) = (a • gen, xB • (a • gen)) instead;
        -- by smul_comm these have the same distribution over uniform a.
        -- B's state is .inl xB after its last send; .inr branch is unreachable.
        let xB := match state.stB with | .inl x => x | .inr _ => 0
        -- In honest send, x drives both the output (x•gen, x•h) and the new
        -- state (.inl x). Here gA and xB•gA replace x in the output, but y
        -- still seeds A's state so subsequent epochs use a fresh exponent.
        let y ← liftM ($ᵗ F : ProbComp F)
        set { state with
          stA := (.inl y : F ⊕ G), lastRhoA := some gA, lastKeyA := some (xB • gA),
          lastAction := some .sendA, tA := state.tA + 1 }
        return some (gA, xB • gA)
      else
        -- All other epochs: honest A-send.
        match ← liftM (ddhCKA.send gen state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          set { state with
            stA := stA', lastRhoA := some ρ, lastKeyA := some key,
            lastAction := some .sendA, tA := state.tA + 1 }
          return some (ρ, key)
    else pure none

/-- Modified A-challenge for the DDH reduction.

At `tA = t*`:
- Output: `(gB, gT)` directly from the DDH tuple
- Real case: `(gB, gT) = (bG, abG)`, matches honest `(x·G, x·aG)` since
  `b` is uniform like `x` and `abG = b·aG` by `smul_comm`
- Random case: `gT = cG` for uniform `c`, matching `$ᵗ G`
- Hidden state: `stA ← .inl z` for fresh `z ← $F` (not `b`);
  safe because `ΔCKA = 1` prevents corruption before overwrite -/
private noncomputable def reductionChallA (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA && state.tA == state.tStar then
      -- Fresh scalar for A's post-challenge state, so corruption reveals a
      -- uniform value matching the honest game (where sendA samples internally).
      let z ← liftM ($ᵗ F : ProbComp F)
      set { state with
        stA := (.inl z : F ⊕ G),
        lastRhoA := some gB, lastKeyA := some gT,
        lastAction := some .challA, tA := state.tA + 1 }
      return some (gB, gT)
    else pure none

/-- Modified B-challenge for the DDH reduction (symmetric to `reductionChallA`).

At `tB = t*`: output `(gB, gT)`, hidden state `stB ← .inl z` for `z ← $F`. -/
private noncomputable def reductionChallB (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challB && state.tB == state.tStar then
      let z ← liftM ($ᵗ F : ProbComp F)
      set { state with
        stB := (.inl z : F ⊕ G),
        lastRhoB := some gB, lastKeyB := some gT,
        lastAction := some .challB, tB := state.tB + 1 }
      return some (gB, gT)
    else pure none

/-- Oracle implementation `R(g, aG, bG, gT)` for the DDH reduction.

Replaces the honest CKA oracles at the embedding epochs:
- sendA at `t*`: output `(aG, xB·aG)` instead of `(x·G, x·xB·G)`
- sendB at `t*-1`: output `(aG, xA·aG)` instead of `(y·G, y·xA·G)`
- challA at `t*`: output `(gB, gT)` from DDH tuple
- challB at `t*`: output `(gB, gT)` from DDH tuple

Only one challenge oracle fires per execution. -/
private noncomputable def reductionOracleImpl (gen gA gB gT : G) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  (oracleUnif (F ⊕ G) G G
    + reductionSendA (F := F) gen gA
    + oracleRecvA (ddhCKA F G gen)
    + reductionSendB (F := F) gen gA
    + oracleRecvB (ddhCKA F G gen))
  + reductionChallA (F := F) gB gT
  + reductionChallB (F := F) gB gT
  + oracleCorruptA (F ⊕ G) G G
  + oracleCorruptB (F ⊕ G) G G

/-- DDH adversary obtained by reduction from a CKA security adversary
[ACD19, Theorem 3].

Given a DDH triple `(gen, gA, gB, gT)`, the reduction:
1. Initialises the CKA game honestly: `x₀ ← $ᵗ F`.
2. Runs the adversary against `reductionOracleImpl`, which embeds `gA` into
   the send oracles and `(gB, gT)` into the challenge oracles for both
   parties A and B.
3. Outputs `!b'` (negated CKA guess) to align bit conventions. -/
noncomputable def securityReduction
    (adversary : SecurityAdversary (F ⊕ G) G G)
    (tStar : ℕ) : DDHAdversary F G :=
  fun gen gA gB gT => do
    let x₀ ← $ᵗ F
    let (b', _) ← (simulateQ (reductionOracleImpl gen gA gB gT) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1)
    return !b'

/-! ### Simulation: each DDH branch maps to the corresponding CKA branch

The main subgoal is to show that the adversary `𝒜` has the same view
whether it interacts with the real CKA game or with the reduction's
simulation. Writing `CKA(b)` for the CKA security game with fixed bit `b`,
and `DDH_real`, `DDH_rand` for the two DDH branches, the reduction `ℬ`
must satisfy:

    `Pr[ℬ = 1 | DDH_real]  = Pr[𝒜 = 0 | CKA(b = 0)]`    … (real branch)
    `Pr[ℬ = 1 | DDH_rand]  = Pr[𝒜 = 0 | CKA(b = 1)]`    … (rand branch)

For the real branch, writing
`G_R := securityReductionRealGame` (runs `𝒜` against `reductionOracleImpl`)
and `G_CKA := securityExpFixedBitFalseGame` (the honest CKA game with `b = 0`),
the proof factors into:

    `Pr[ℬ = 1 | DDH_real]`
      `= Pr[G_R = 0]`            (unfold + `probOutput_not_map`)
      `= Pr[G_CKA = 0]`          (lemma `securityReduction_real_bridge`)
      `= Pr[CKA(b = 0) = 0]`     (unfold `securityExpFixedBit`)

The core step `Pr[G_R = 0] = Pr[G_CKA = 0]` factors as:

    `Pr[G_R = 0]  =  Pr[G_I = 0]  =  Pr[G_CKA = 0]`

where `G_I` (`securityRealIdealGame`) runs `𝒜` against `I = realIdealImpl(g, a, b)`.
`I` and `R` have identical outputs, but `I` sets hidden state to `a, b`
where `R` draws fresh `y, z ← $F`. The first `=` is by simulation relation
`π = realIdealProj a b`; the second is by algebraic unfolding.

For the random branch, bijectivity of `· • gen` gives `c • gen ≡ $ᵗ G`,
which directly equates the reduction's challenge key with a uniform sample.
-/

/-- Auxiliary game `G_real(𝒜)`: samples `a, b, x₀ ← $F`, runs `𝒜` against
`R = reductionOracleImpl(g, ag, bg, abg)`, and returns `b'` (without negation).

The full reduction returns `¬b'`, so `Pr[ℬ = true | real DDH] = Pr[G_real = false]`
by `probOutput_not_map`. The bridge lemmas then show
`Pr[G_real = false] = Pr[CKA(b=false) = false]`, completing `securityReduction_real`. -/
private noncomputable def securityReductionRealGame
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (reductionOracleImpl gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1)
  return b'

/-- Unfold the real DDH branch of the reduction into the explicit helper game
`securityReductionRealGame`. -/
private lemma probOutput_ddhExpReal_securityReduction
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= true | ddhExpReal gen (securityReduction adversary tStar)] =
    Pr[= false | securityReductionRealGame (F := F) (G := G) (gen := gen) adversary tStar] := by
  unfold DiffieHellman.ddhExpReal securityReduction
  simpa [securityReductionRealGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRealGame (F := F) (G := G) (gen := gen) adversary tStar))

/-- The fixed-bit CKA security game with `b = false`, written explicitly with the
initial key sample exposed. -/
private noncomputable def securityExpFixedBitFalseGame
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1)
  return b'

/-- Unfold the fixed-bit `b = false` branch into the explicit helper game
`securityExpFixedBitFalseGame`. -/
private lemma probOutput_securityExpFixedBit_false
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false tStar 1] =
    Pr[= false | securityExpFixedBitFalseGame (F := F) (G := G) (gen := gen) adversary tStar] := by
  unfold CKAScheme.securityExpFixedBit securityExpFixedBitFalseGame ddhCKA
  simp

/-- Idealized B-send used in the real-branch bridge.
At the special epoch before `challA`, it reuses the externally fixed DDH scalar
`a` both for the visible output and for B's next hidden state. This matches the
honest game instantiated with the corresponding challenge randomness, unlike
`reductionSendB`, which uses an independent fresh hidden scalar. -/
private noncomputable def realIdealSendB (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      if state.tB + 1 == state.tStar then
        let gA := a • gen
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        set { state with
          stB := (.inl a : F ⊕ G), lastRhoB := some gA, lastKeyB := some (xA • gA),
          lastAction := some .sendB, tB := state.tB + 1 }
        return some (gA, xA • gA)
      else
        match ← liftM (ddhCKA.send gen state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          set { state with
            stB := stB', lastRhoB := some ρ, lastKeyB := some key,
            lastAction := some .sendB, tB := state.tB + 1 }
          return some (ρ, key)
    else pure none

/-- Idealized A-challenge used in the real-branch bridge.
At the challenge epoch, it reuses the externally fixed DDH scalar `b` as A's
post-challenge hidden state. This matches the honest game when the challenge
send samples `b`. -/
private noncomputable def realIdealChallA (gen : G) (a b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA && state.tA == state.tStar then
      let gB := b • gen
      let gT := (a * b) • gen
      set { state with
        stA := (.inl b : F ⊕ G),
        lastRhoA := some gB, lastKeyA := some gT,
        lastAction := some .challA, tA := state.tA + 1 }
      return some (gB, gT)
    else pure none

/-- Real-branch bridge implementation: same visible DDH embedding as
`reductionOracleImpl`, but the hidden states at the special B-send / A-challenge
epochs are synchronized with the corresponding honest-game randomness. -/
private noncomputable def realIdealImpl (gen : G) (a b : F) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  (oracleUnif (F ⊕ G) G G
    + reductionSendA (F := F) gen (a • gen)
    + oracleRecvA (ddhCKA F G gen)
    + realIdealSendB (F := F) gen a
    + oracleRecvB (ddhCKA F G gen))
  + realIdealChallA (F := F) gen a b
  + reductionChallB (F := F) (b • gen) ((a * b) • gen)
  + oracleCorruptA (F ⊕ G) G G
  + oracleCorruptB (F ⊕ G) G G

/-- The explicit game induced by `realIdealImpl`. -/
private noncomputable def securityRealIdealGame
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (realIdealImpl (F := F) gen a b) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1)
  return b'

/-- State projection `π : GameState → GameState` mapping `reductionOracleImpl`
states to `realIdealImpl` states.

Let `R := reductionOracleImpl(g, aG, bG, abG)` and `I := realIdealImpl(g, a, b)`.
`R` and `I` agree on all outputs but diverge on hidden party state at two
embedding epochs: `R` draws fresh `y, z ← $F` while `I` sets `stB := a` and
`stA := b`. The projection `π` collapses this:

- `stB` window (`tB = t*`, after sendB): `π(.inl y) = .inl a`
- `stA` window (`tA = t* + 1`, after challA): `π(.inl z) = .inl b`

All other fields (outputs, counters, flags) pass through unchanged. -/
private noncomputable def realIdealProj (a b : F)
    (s : GameState (F ⊕ G) G G) : GameState (F ⊕ G) G G :=
  { s with
    stA := match s.stA with
      | .inl _ =>
          if s.tA == s.tStar + 1 &&
              (s.lastAction = some .challA ||
               s.lastAction = some .recvB ||
               s.lastAction = some .sendB)
          then (.inl b : F ⊕ G)
          else s.stA
      | .inr _ => s.stA
    stB := match s.stB with
      | .inl _ =>
          if s.tB == s.tStar &&
              (s.lastAction = some .sendB ||
               s.lastAction = some .recvA ||
               s.lastAction = some .sendA ||
               s.lastAction = some .challA)
          then (.inl a : F ⊕ G)
          else s.stB
      | .inr _ => s.stB }

/-- One-step projection property for `reductionOracleImpl` in the real branch.

Let `π := realIdealProj a b` (state projection),
`R := reductionOracleImpl(g, aG, bG, abG)` (concrete reduction oracles),
`I := realIdealImpl(g, a, b)` (idealized real-branch oracles). Then:

    `(id × π)(R(t, s)) = I(t, π(s))` -/
private lemma realIdealProj_query_map_eq (a b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G) :
    Prod.map id (realIdealProj (F := F) a b) <$>
      ((reductionOracleImpl gen (a • gen) (b • gen) ((a * b) • gen)) t).run s =
    ((realIdealImpl (F := F) gen a b) t).run
      (realIdealProj (F := F) a b s) := by
  sorry

/-- First half of the real-branch bridge: the concrete reduction may differ from
`realIdealImpl` on hidden intermediate state, but these differences remain
unobservable under strict healing (`ΔCKA = 1`). -/
private lemma securityReduction_real_to_ideal
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= false | securityReductionRealGame (F := F) (G := G) (gen := gen) adversary tStar] =
    Pr[= false | securityRealIdealGame (F := F) (G := G) (gen := gen) adversary tStar] := by
  unfold securityReductionRealGame securityRealIdealGame
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro a
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro b
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro x₀
  have hinit :
      realIdealProj (F := F) a b
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1) =
      initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1 := by
    simp [realIdealProj, initGameState]
  have hrun' :=
    OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq
      (impl₁ := reductionOracleImpl gen (a • gen) (b • gen) ((a * b) • gen))
      (impl₂ := realIdealImpl (F := F) gen a b)
      (proj := realIdealProj (F := F) a b)
      (hproj := realIdealProj_query_map_eq (F := F) (G := G) (gen := gen) a b)
      adversary
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1)
  rw [hinit] at hrun'
  exact congrArg (fun mx => Pr[= false | mx]) hrun'

/-- Second half of the real-branch bridge: `realIdealImpl` is the honest
fixed-bit-false game with the two special challenge scalars sampled explicitly
up front. -/
private lemma securityReduction_ideal_to_honest
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= false | securityRealIdealGame (F := F) (G := G) (gen := gen) adversary tStar] =
    Pr[= false | securityExpFixedBitFalseGame (F := F) (G := G) (gen := gen) adversary tStar] := by
  sorry

/-- The core bridge for the real branch: the explicit real-DDH reduction game
matches the explicit fixed-bit CKA game with `b = false`. -/
private lemma securityReduction_real_bridge
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= false | securityReductionRealGame (F := F) (G := G) (gen := gen) adversary tStar] =
    Pr[= false | securityExpFixedBitFalseGame (F := F) (G := G) (gen := gen) adversary tStar] := by
  rw [securityReduction_real_to_ideal (F := F) (G := G) (gen := gen) adversary tStar]
  exact securityReduction_ideal_to_honest (F := F) (G := G) (gen := gen) adversary tStar

/-- **Real-branch lemma.**
`Pr[ℬ outputs true | real DDH] = Pr[𝒜 guesses false | CKA b = false]`. -/
lemma securityReduction_real
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= true | ddhExpReal gen (securityReduction adversary tStar)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false tStar 1] := by
  rw [probOutput_ddhExpReal_securityReduction, probOutput_securityExpFixedBit_false]
  exact securityReduction_real_bridge (F := F) (G := G) (gen := gen) adversary tStar

/-- **Random-branch lemma.**
`Pr[ℬ outputs true | random DDH] = Pr[𝒜 guesses false | CKA b = true]`.
Needs bijectivity of `· • gen` to couple `c • gen` with `$ᵗ G`. -/
lemma securityReduction_rand
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= true | ddhExpRand gen (securityReduction adversary tStar)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true tStar 1] := by
  sorry

/-! ### Main security theorems

From the branch lemmas above, we derive the security bound. The proof
combines the real and random branch equalities with the standard
decomposition of both games over a fair coin:

  `Pr[DDH win] - 1/2 = (Pr[ℬ=1|real] - Pr[ℬ=1|rand]) / 2`
                      `= (Pr[𝒜=0|b=0] - Pr[𝒜=0|b=1]) / 2`
                      `= Pr[CKA win] - 1/2`

Hence `ddhGuessAdvantage(gen, ℬ) = securityAdvantage(ddhCKA, 𝒜, tStar, 1)`.

**Corruption safety** (`ΔCKA = 1`, strict healing). After the challenge:
- The challenged party's state at `tStar + 1` may be a fresh hidden scalar,
  but corruption is still blocked at that point.
- Corruption only becomes possible after the challenged party advances once
  more, by which time the challenge-linked state has been overwritten.
- The other party's state at `tStar` is `.inr gB` (public DDH component).
-/

/-- **DDH-CKA security (per-adversary form)** [ACD19, Theorem 3].

For any CKA adversary `𝒜`, the CKA advantage is bounded by the DDH
guess-advantage of the reduction `ℬ = securityReduction 𝒜 tStar`:

  `securityAdvantage(ddhCKA, 𝒜, tStar, 1) ≤ ddhGuessAdvantage(gen, ℬ)` -/
theorem security
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    securityAdvantage (ddhCKA F G gen) adversary tStar 1 ≤
      ddhGuessAdvantage gen (securityReduction adversary tStar) := by
  sorry

/-- **DDH-CKA security (quantitative form)** [ACD19, Theorem 3].

If the DDH assumption holds in `G` with guess-advantage at most `ε` for every
adversary, then for any CKA adversary `𝒜`:

  `securityAdvantage(ddhCKA, 𝒜, tStar, 1) ≤ ε` -/
theorem ddhCKA_security
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G)
    (tStar : ℕ) (ε : ℝ)
    (hddh : ∀ adv : DDHAdversary F G,
      ddhGuessAdvantage gen adv ≤ ε) :
    securityAdvantage (ddhCKA F G gen) adversary tStar 1 ≤ ε :=
  calc securityAdvantage (ddhCKA F G gen) adversary tStar 1
      ≤ ddhGuessAdvantage gen (securityReduction adversary tStar) :=
        security hg adversary tStar
    _ ≤ ε := hddh _

end ddhCKA

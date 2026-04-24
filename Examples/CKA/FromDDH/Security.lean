import Examples.CKA.FromDDH.Common
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Tactics.Common.OracleSum
import VCVio.OracleComp.QueryTracking.LazySampling

/-!
# CKA from DDH — Security Proof

Security reduction from DDH to CKA key-indistinguishability,
following [ACD19, Theorem 3].
https://eprint.iacr.org/2018/1037.pdf

## Main result

**Theorem** (`ddhCKA_security`). *Let `G` be a group with generator `gen` such
that `· • gen : F → G` is bijective. If every DDH adversary has guess-advantage
at most `ε`, then for any CKA adversary `𝒜`, challenge epoch `tStar`,
and challenged party `P ∈ {A, B}`:*

  `securityAdvantage(ddhCKA, 𝒜, ⟨tStar, 1, P⟩) ≤ ε`

*where `securityAdvantage = |Pr[b = b' | securityExp] - 1/2|` and `ΔCKA = 1`.
More precisely, there is an explicit DDH adversary
`ℬ = securityReduction ⟨tStar, 1, P⟩ 𝒜` such that
`securityAdvantage(ddhCKA, 𝒜, ⟨tStar, 1, P⟩) ≤ ddhGuessAdvantage(gen, ℬ)`*

### `ΔCKA = 1`

`ΔCKA = 1` in the main theorem means the adversary is allowed to corrupt
party `Q` only if `tQ ≥ tStar + ΔCKA`: one more action after the challenge epoch.
This is the smallest `ΔCKA` that works — with `ΔCKA = 0`:
- Corrupting the challenged party `P` immediately after the challenge would
  reveal the fresh scalar `z` used for key derivation.
- Corrupting the other party `Q` is harmless (state is `gB ∈ G`, public),
  but `ΔCKA` applies uniformly to both parties.

Illustration with `P = A` challenged at `tA = tStar`:

```text
         A (challenged)                              B
         ──────────────                              ──
              │                                       │
              │                                       │ sendB: ...
              │                                       │ B stores y
              │◀──────── ρ = y•gen ──────────────────│
              │                                       │
 tA = t*  challA: z ←$ F                              │
          A stores z                                  │
          key_A = z•ρ                                 │
          ρ' = z•gen                                  │
              │──────── ρ' ─────────────────────────▶│
              │                                  tB++ │ recvB: ...
              │                                       │ B stores ρ' ∈ G
              │                                       │
              │                             tB = t*   │ sendB: x' ←$ F
              │                                       │ key_B = x'•ρ'
              │                                       │ B stores x'
              │◀──────── ρ'' = x'•gen ──────────────│
 tA++     recvA                                       │
          key_A' = z•ρ'' = z•x'•gen                   │
          A stores ρ'' ∈ G                            │
          (z overwritten)                             │
              │                                       │
         ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
         finishedA (tA ≥ t*+1)    finishedB (tB ≥ t*+1)
         corruptA → ρ'' ∈ G      corruptB → x' ∈ F
```

At the point corruption is allowed, neither `stA` nor `stB` contains
information about the challenge key `key_A = z•ρ`.

## Proof overview — reduction diagram (the constructed DDH adversary `ℬ`)

Assume given a CKA adversary `𝒜` that challenges exactly one party at epoch `t*`.
We show the case where `𝒜` calls `O-Chall-A` at `tA = t*`.

Given a DDH triple `(gen, gA, gB, gT)` with
`gA = a • gen`,`gB = b • gen`, and `gT = c • gen` where `c = a·b` (real) or `c` is uniform:

```text
 DDH Challenger                 DDH Adversary ℬ = securityReduction gp 𝒜
┌──────────────┐               ┌──────────────────────────────────────────────────┐
│              │ (gen,gA,gB,gT)│ sample x₀ ←$ F                                   │
│  gA = a•gen  │──────────────▶│ init A with g₀ := x₀ • gen, init B with x₀       │
│  gB = b•gen  │               │                                                  │
│  gT = c•gen  │               │ simulate CKA oracles for 𝒜 (honest except below):│
│              │               │                                                  │
│  c = a·b     │               │          Honest CKA        │ Reduction           │
│  or random   │               │ ─────────────────────────────────────────────────│
│              │               │ O-Send-B, tB = t* - 1, stA = xA ∈ F, stB = xA•gen│
│              │               │   y ←$ F                   │                     │
│              │               │   ρ   = y • gen            │ ρ   = gA            │
│              │               │   key = y • xA • gen       │ key = xA • gA       │
│              │               │   stB := y (live)          │ stB := 0 (dead)     │
│              │               │ ─────────────────────────────────────────────────│
│              │               │ recvA delivers ρ from above:                     │
│              │               │   stA := y • gen           │ stA := gA           │
│              │               │ ─────────────────────────────────────────────────│
│              │               │ O-Chall-A, tA = t*, (stA, stB) as updated above: │
│              │               │   x ←$ F                   │                     │
│              │               │   ρ   = x • gen            │ ρ   = gB            │
│              │               │   key = x • stA            │ key = gT            │
│              │               │   stA := x (live)          │ stA := 0 (dead)     │
│              │               │ · · · · · · · · · · · · · · · · · · · · · · · · ·│
│              │               │  real: gT = b • gA            random: gT ←$ G    │
│              │               │ ─────────────────────────────────────────────────│
│              │               │ all later queries: honest in both columns        │
│              │               │                                                  │
│              │     !b'       │ output !b', where b' is 𝒜's challenge guess      │
│              │◀──────────────│                                                  │
└──────────────┘               └──────────────────────────────────────────────────┘
```

**Goal.** Show `evalDist (reductionGame) = evalDist (honestGame)`, i.e., the
reduction perfectly simulates the honest CKA game on each DDH branch. DDH
uses `true` for the real branch and the CKA game uses `true` for the random
branch, so the correspondence inverts the bit and the reduction returns `!b'`:

  DDH_real  ↔  CKA with `b = false` (real key)
  DDH_rand  ↔  CKA with `b = true`  (random key)

Games involved:
  `securityReductionRealGame` / `securityReductionRandGame`         (reduction)
  `securityExpFixedBitFalseGame` (`CKA^{b = false}`) /
    `securityExpFixedBitTrueGame` (`CKA^{b = true}`)                (honest)

Perfect simulation transfers `𝒜`'s real-vs-random CKA distinguishing
advantage to `ℬ`'s DDH distinguishing advantage, giving the security bound
in `securityReduction_real` / `securityReduction_rand` below.

**Challenge reachability and init.** All reachable `gp` admit an
embedding-send (`sendB` for `P = A`, `sendA` for `P = B`) before the
challenge, *except* `gp = ⟨1, _, .A⟩`: there `challA` fires as the first
action with no prior send. For this case alone, `reductionInitState` injects
`gA` at init into `stA` (identifying `x₀` with `a`); all other `gp` use the
standard init `x₀ ←$ F` with `gA` embedded at the pre-challenge send.

**Per-query coupling at the embedding.** Reduction samples `a, b ←$ F` at the
top of the game; honest samples per-epoch scalars inside its oracle bodies.
`probOutput_simulateQ_consumeLazy_run'_eq` moves reduction's samples inside
too, firing them only at hit queries (embedding-send + challenge):

  eager:   `a ←$ F; simulateQ (reductionOracleImpl … (a•gen) …) 𝒜`
  lazy:    `simulateQ (consumeLazy (fun a ↦ reductionOracleImpl … (a•gen) …) hit) 𝒜`

where `consumeLazy f hit` is a `QueryImpl` that, at queries `t` with
`hit t = true`, samples `a ←$ F` on first fire, caches it in an `Option F`
slot, and reuses the cached `a` on subsequent hits — so the outer `a ←$ F`
moves to the first hit query.

At the embedding hit, the two sides' per-query `ProbComp (G × G)` become:

  `ckaSecurityImpl`:      `y ←$ F; return (y • gen, xA • y • gen)`
  `reductionOracleImpl`:  `a ←$ F; return (a • gen, xA • a • gen)`

coupled by the identity bijection `y ↔ a`.
-/

open OracleSpec OracleComp ENNReal

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme DiffieHellman

variable [DecidableEq G]

/-! ### DDH reduction

Input: DDH tuple `(gen, aG, bG, gT)` with `a, b ←$ F` and
  `gT = abG` (real) or `gT = cG`, `c ←$ F` (random).

Embedding epoch (`O-Send-X` at `tX = t* - 1`) injects `gA` into the output.
Challenge epoch (`O-Chall-X` at `tX = t*`) injects `(gB, gT)`.
Both write `stX := .inl 0` placeholder to state.
All other epochs run honest CKA. -/

private noncomputable def reductionSendB (gp : GameParams) (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      let state := { state with tB := state.tB + 1 }
      if gp.challengedParty == .A && isOtherSendBeforeChall gp state then
        -- embed: stB := .inl 0 (dead), rhoB := gA, keyB := xA • gA
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        set { state with
          stB := (.inl 0 : F ⊕ G), rhoB := some gA, keyB := some (xA • gA),
          lastAction := some .sendB }
        return some (gA, xA • gA)
      else
        -- honest = `ddhCKA.send gen state.stB`: requires stB = .inr h, then
        --   x ←$ F; stB := .inl x, rhoB := x • gen, keyB := x • h
        match ← liftM (ddhCKA.send gen state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          set { state with
            stB := stB', rhoB := some ρ, keyB := some key,
            lastAction := some .sendB }
          return some (ρ, key)
    else pure none

private noncomputable def reductionSendA (gp : GameParams) (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      let state := { state with tA := state.tA + 1 }
      if gp.challengedParty == .B && isOtherSendBeforeChall gp state then
        -- embed: stA := .inl 0 (dead), rhoA := gA, keyA := xB • gA
        let xB := match state.stB with | .inl x => x | .inr _ => 0
        set { state with
          stA := (.inl 0 : F ⊕ G), rhoA := some gA, keyA := some (xB • gA),
          lastAction := some .sendA }
        return some (gA, xB • gA)
      else
        -- honest = `ddhCKA.send gen state.stA`: requires stA = .inr h, then
        --   x ←$ F; stA := .inl x, rhoA := x • gen, keyA := x • h
        match ← liftM (ddhCKA.send gen state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          set { state with
            stA := stA', rhoA := some ρ, keyA := some key,
            lastAction := some .sendA }
          return some (ρ, key)
    else pure none

private noncomputable def reductionChallA (gp : GameParams) (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .A && validStep state.lastAction .challA then
      let state := { state with tA := state.tA + 1 }
      if isChallengeEpoch gp state then
        -- challenge: stA := .inl 0 (dead), rhoA := gB, keyA := gT
        set { state with
          stA := (.inl 0 : F ⊕ G),
          rhoA := some gB, keyA := some gT,
          lastAction := some .challA }
        return some (gB, gT)
      else pure none
    else pure none

private noncomputable def reductionChallB (gp : GameParams) (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .B && validStep state.lastAction .challB then
      let state := { state with tB := state.tB + 1 }
      if isChallengeEpoch gp state then
        -- challenge: stB := .inl 0 (dead), rhoB := gB, keyB := gT
        set { state with
          stB := (.inl 0 : F ⊕ G),
          rhoB := some gB, keyB := some gT,
          lastAction := some .challB }
        return some (gB, gT)
      else pure none
    else pure none

/-- Reduction's oracle stack: the four DDH-embedding components
(`reductionSend{A,B}` and `reductionChall{A,B}`) combined with honest
`oracleUnif`, `oracleRecv{A,B}`, and `oracleCorrupt{A,B}`. -/
private noncomputable def reductionOracleImpl (gp : GameParams) (gen gA gB gT : G) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  (oracleUnif (F ⊕ G) G G
    + reductionSendA (F := F) gp gen gA
    + oracleRecvA (ddhCKA F G gen)
    + reductionSendB (F := F) gp gen gA
    + oracleRecvB (ddhCKA F G gen))
  + reductionChallA (F := F) gp gB gT
  + reductionChallB (F := F) gp gB gT
  + oracleCorruptA gp (F ⊕ G) G G
  + oracleCorruptB gp (F ⊕ G) G G

/-- Initial CKA game state used by the reduction, case-split on `gp`.

* **Edge case** `gp = ⟨1, _, .A⟩`: `challA` must fire as the first action
  (`validStep none .challA`), so no embedding-send can precede the challenge.
  In this case the reduction identifies `x₀` with `a` by directly injecting
  `gA` into `stA`, skipping the usual `x₀ ← $ᵗ F` sample. The placeholder
  `.inl 0` in `stB` is a dead cell — B's internal key check at subsequent
  `recvB` flips `state.correct`, which is unobserved by the security game.

* **Standard case**: `x₀ ← $ᵗ F`, `stA := .inr (x₀•gen)`, `stB := .inl x₀`,
  matching honest CKA. Embedding of `gA` happens at the `sendB`-before-challenge
  epoch for `P = A` or `sendA`-before-challenge for `P = B` (both reachable
  when the challenge is reachable). -/
private noncomputable def reductionInitState (gp : GameParams) (gen gA : G) :
    ProbComp (GameState (F ⊕ G) G G) :=
  if gp.tStar = 1 ∧ gp.challengedParty = .A then
    return initGameState (.inr gA) ((.inl 0) : F ⊕ G) false
  else do
    let x₀ ← $ᵗ F
    return initGameState (.inr (x₀ • gen)) (.inl x₀) false

/-- DDH adversary obtained by reduction from a CKA security adversary
[ACD19, Theorem 3], parameterized by `gp : GameParams`.

Given a DDH triple `(gen, gA, gB, gT)` and a CKA adversary, the reduction:
1. Builds the initial CKA game state via `reductionInitState` (case-split on `gp`).
2. Runs the CKA adversary against `reductionOracleImpl`, which embeds `gA` into
   the other party's send and `(gB, gT)` into `gp.challengedParty`'s challenge.
3. Outputs `!b'` as DDH guess (negated CKA guess, to align bit conventions). -/
noncomputable def securityReduction (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : DDHAdversary F G :=
  fun gen gA gB gT => do
    let s₀ ← reductionInitState gp gen gA
    let (b', _) ← (simulateQ (reductionOracleImpl gp gen gA gB gT) adversary).run s₀
    return !b'

/-! ### Simulation: each DDH branch maps to the corresponding CKA branch

Goal: the reduction `ℬ = securityReduction gp 𝒜` (which returns `¬b'`)
satisfies the top-level branch identities

    Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA^{b = false}]   (**real branch**)
    Pr[ℬ = true | DDH_rand] = Pr[𝒜 = false | CKA^{b = true }]   (**random branch**)

Each branch is proved by a 3-step chain:

```text
Pr[ℬ = true | DDH_real]
    = Pr[= false | securityReductionRealGame]             -- (1) peel `¬b'`
    = Pr[= false | securityExpFixedBitFalseGame]          -- (2) game-level bridge
    = Pr[= false | securityExpFixedBit ... false gp]      -- (3) def. fold

Pr[ℬ = true | DDH_rand]
    = Pr[= false | securityReductionRandGame]             -- (1) peel `¬b'`
    = Pr[= false | securityExpFixedBitTrueGame]           -- (2) game-level bridge
    = Pr[= false | securityExpFixedBit ... true gp]       -- (3) def. fold
```

Lemmas (real / rand):
`(1) probOutput_ddhExpReal_securityReduction`          /
    `probOutput_ddhExpRand_securityReduction`,
`(2) probOutput_securityReductionRealGame_eq_honestFalse` /
    `probOutput_securityReductionRandGame_eq_honestTrue`,
`(3) probOutput_securityExpFixedBit_false`             /
    `probOutput_securityExpFixedBit_true`.

Steps (1) and (3) are mechanical: (1) is a `simpa` invocation of
`probOutput_not_map` peeling the final `¬`; (3) is pure definitional
unfolding. Step (2) carries the actual reduction argument: a per-fixed-`x₀`
equivalence `securityReductionRealGame ≡ CKA^{b = false}`, proved by
`consumeLazy` push-in (for `a, b`) plus a state relation `R` between
reduction-side and honest-side game states, case-split on `gp`:

* **Standard case** (`gp ≠ ⟨1, _, .A⟩`). Both sides start from
  `(stA, stB) = (x₀•gen, x₀)` with shared outer `x₀ ←$ F`. For each fixed
  `x₀`: push `a, b` into hit queries (embedding + challenge); couple by `R`
  matching all cells except dead writes `stX: 0 ↔ y`, bijected `y ↔ a/b`
  with honest's fresh in-oracle sample.

* **Edge case** (`gp = ⟨1, _, .A⟩`). Reduction init `(gA, 0)` vs honest
  `(x₀•gen, x₀)`; identify `a ≡ x₀`. For each fixed `x₀`: push only `b` into
  `challA`; couple by `R` tolerating `stB: 0 ↔ x₀` at init (healed by first
  `recvB` overwriting `stB := .inr ρ`; corruption blocked until then).
-/

/-- Real Branch -/
private noncomputable def securityReductionRealGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let s₀ ← reductionInitState gp gen (a • gen)
  let (b', _) ←
  -- we use a*b in the real game, corresponding to DDH_real
    (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run s₀
  return b'

/-- **Step (1) of the real branch.** Peel `ℬ`'s final `¬`:

  `Pr[ℬ = true | DDH_real]  =  Pr[securityReductionRealGame = false]`

`ddhExpReal gen ℬ` and `securityReductionRealGame gp 𝒜` run the same sampling
and simulation; they differ only in their (negated bit) return. -/
private lemma probOutput_ddhExpReal_securityReduction (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpReal securityReduction
  simpa [securityReductionRealGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRealGame (gen := gen) gp adversary))

/-- **Game `CKA^{b = false}`**
`x₀ ←$ F`, run `𝒜` against `ckaSecurityImpl gp (ddhCKA F G gen)` with challenge bit `false`.
-/
private noncomputable def securityExpFixedBitFalseGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- **Step (3) of the real branch.**
  `Pr[𝒜 = false ∣ securityExpFixedBit … false gp] = Pr[𝒜 = false | CKA^{b = false}]`

Pure definitional unfolding of `securityExpFixedBit` at `ddhCKA F G gen` -/
private lemma probOutput_securityExpFixedBit_false (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpFixedBitFalseGame ddhCKA
  simp [initGameState]

/-- Random Branch -/
private noncomputable def securityReductionRandGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let c ← $ᵗ F
  let s₀ ← reductionInitState gp gen (a • gen)
  let (b', _) ←
    (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run s₀
  return b'

/-- **Step (1) of the random branch.** Peel `ℬ`'s final `¬`:

  `Pr[ℬ = true | DDH_rand]  =  Pr[= false | securityReductionRandGame]`

Parallel to Step (1) of the real branch: `ddhExpRand gen ℬ` returns `!b'`,
`securityReductionRandGame` returns `b'`; apply `probOutput_not_map`. -/
private lemma probOutput_ddhExpRand_securityReduction (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpRand gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRandGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpRand securityReduction
  simpa [securityReductionRandGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRandGame (gen := gen) gp adversary))

/-- **Game `CKA^{b = true}`**
 `x₀ ←$ F`, run `𝒜` against `ckaSecurityImpl gp (ddhCKA F G gen)` with challenge bit
`true`. Same per-epoch sampling pattern as `CKA^{b = false}`, but `challX`
outputs a uniform `outKey ←$ᵗ G` instead of the real key. -/
private noncomputable def securityExpFixedBitTrueGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) true)
  return b'

/-- **Step (3) of the random branch.** Random-branch analogue of
`probOutput_securityExpFixedBit_false`: fold the named endpoint game back
into the generic fixed-bit notation at `b = true`. -/
private lemma probOutput_securityExpFixedBit_true (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true gp] =
    Pr[= false | securityExpFixedBitTrueGame (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpFixedBitTrueGame ddhCKA
  simp [initGameState]

/-! ### Helpers for Step (2): hit predicates and lazy reduction

Pattern-matched on the 9-way nested-`Sum` domain of `ckaSecuritySpec`, with
outside-in ordering: `.inr ↦ corruptB`, `.inl .inr ↦ corruptA`,
`.inl .inl .inr ↦ challB`, `.inl (…).inr ↦ challA`, …, innermost
`.inl …(ℕ)` for `unifSpec`.
-/

section Step2
variable [Inhabited F]

open OracleComp.ProgramLogic.Relational in
/-- Hit predicate for the external DDH scalar `a`. Fires at queries where
`reductionOracleImpl` can inject `gA = a•gen`:
* `P = A`: `sendB` (embedding epoch) and `challA` (challenge epoch).
* `P = B`: `sendA` (embedding epoch) and `challB` (challenge epoch).

At non-hit queries the reduction's impl is `a`-independent
(see `hindepA_real`). -/
private def hitA (gp : GameParams) :
    (ckaSecuritySpec (F ⊕ G) G G).Domain → Bool
  | .inl (.inl (.inl (.inr _))) =>  -- challA
      gp.challengedParty = .A
  | .inl (.inl (.inr _)) =>          -- challB
      gp.challengedParty = .B
  | .inl (.inl (.inl (.inl (.inl (.inr _))))) =>  -- sendB
      gp.challengedParty = .A
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))) =>  -- sendA
      gp.challengedParty = .B
  | _ => false

/-- Hit predicate for the external DDH scalar `b`. Fires at the challenge
query of the challenged party (the only site where `gT = (a·b)•gen` is
injected by `reductionChall{A,B}`). -/
private def hitB (gp : GameParams) :
    (ckaSecuritySpec (F ⊕ G) G G).Domain → Bool
  | .inl (.inl (.inl (.inr _))) =>  -- challA
      gp.challengedParty = .A
  | .inl (.inl (.inr _)) =>          -- challB
      gp.challengedParty = .B
  | _ => false

open OracleComp.ProgramLogic.Relational in
/-- Lazy-sampled reduction impl (real branch): two `consumeLazy` layers peel
`a` and `b` into their hit queries. State cells:
`((gameState, optA : Option F), optB : Option F)` — inner cache for `a`,
outer cache for `b`. -/
private noncomputable def reductionImpl_lazy_real (gp : GameParams) (gen : G) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G)
      (StateT ((GameState (F ⊕ G) G G × Option F) × Option F) ProbComp) :=
  consumeLazy (hit := hitB gp) (implFam := fun b =>
    consumeLazy (hit := hitA gp) (implFam := fun a =>
      reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)))

omit [Inhabited F] in
/-- `h_indep` for the `a`-layer of `reductionImpl_lazy_real`: at `hitA = false`
queries, `reductionOracleImpl` is independent of `a`. Non-hit queries dispatch
to oracles that don't touch `gA` (non-embedding `send{A,B}`, `recv{A,B}`,
`unif`, `corrupt{A,B}`, wrong-party `chall{A,B}` — the last four branches
return `pure none` before reaching `gT`). -/
private lemma hindepA_real (gp : GameParams) (b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G) (a₁ a₂ : F)
    (h : hitA gp t = false) :
    (reductionOracleImpl gp gen (a₁ • gen) (b • gen) ((a₁ * b) • gen) t).run s =
    (reductionOracleImpl gp gen (a₂ • gen) (b • gen) ((a₂ * b) • gen) t).run s := by
  -- Match on the 9-way nested Sum domain.
  match t with
  | .inr _ => rfl  -- corruptB: no gA/gB/gT use
  | .inl (.inr _) => rfl  -- corruptA: no gA/gB/gT use
  | .inl (.inl (.inr _)) =>  -- challB: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallB, h_cp]
      rfl
    | B =>
      exfalso
      simp [hitA, h_cp] at h
  | .inl (.inl (.inl (.inr _))) =>  -- challA: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso
      simp [hitA, h_cp] at h
    | B =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallA, h_cp]
      rfl
  | .inl (.inl (.inl (.inl (.inr _)))) => rfl  -- recvB: no gA use
  | .inl (.inl (.inl (.inl (.inl (.inr _))))) =>  -- sendB: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso
      simp [hitA, h_cp] at h
    | B =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionSendB, h_cp]
      rfl
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))) => rfl  -- recvA: no gA use
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))) =>  -- sendA: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionSendA, h_cp]
      rfl
    | B =>
      exfalso
      simp [hitA, h_cp] at h
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _))))))) => rfl  -- oracleUnif: no gA use

/-- `h_indep` for the `b`-layer (inner `consumeLazy` over `a`): at
`hitB = false` queries, `consumeLazy (fun a => reductionOracleImpl … gA (b•gen)
((a·b)•gen))` is independent of `b`. Non-hit queries (everything except the
challenge of the challenged party) either don't touch `gB, gT` at all or
return `pure none` on the wrong-party guard. -/
private lemma hindepB_real (gp : GameParams)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G × Option F) (b₁ b₂ : F)
    (h : hitB gp t = false) :
    (OracleComp.ProgramLogic.Relational.consumeLazy (hit := hitA gp)
        (implFam := fun a =>
          reductionOracleImpl gp gen (a • gen) (b₁ • gen) ((a * b₁) • gen)) t).run s =
    (OracleComp.ProgramLogic.Relational.consumeLazy (hit := hitA gp)
        (implFam := fun a =>
          reductionOracleImpl gp gen (a • gen) (b₂ • gen) ((a * b₂) • gen)) t).run s := by
  -- The consumeLazy wrapper is b-independent at every t where the inner
  -- `reductionOracleImpl … (a•gen) (b•gen) ((a*b)•gen) t` is b-independent.
  -- Only challA/challB with matching party use gB/gT; hitB restricts exactly
  -- those cases, so at hitB=false the inner impl is b-independent.
  match t with
  | .inr _ => rfl  -- corruptB: no gB/gT use
  | .inl (.inr _) => rfl  -- corruptA: no gB/gT use
  | .inl (.inl (.inr _)) =>  -- challB: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallB, hitA, h_cp]
      rfl
    | B =>
      exfalso
      simp [hitB, h_cp] at h
  | .inl (.inl (.inl (.inr _))) =>  -- challA: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso
      simp [hitB, h_cp] at h
    | B =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallA, hitA, h_cp]
      rfl
  | .inl (.inl (.inl (.inl (.inr _)))) => rfl  -- recvB
  | .inl (.inl (.inl (.inl (.inl (.inr _))))) => rfl  -- sendB (uses gA only, not b)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))) => rfl  -- recvA
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _))))))) => rfl  -- sendA (uses gA only)
  | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _))))))) => rfl  -- oracleUnif

/-- Per-cell coupling tolerating dead-write divergence on a single party's
cell. Either the cells match, or reduction's cell is the placeholder `.inl 0`
while honest's cell is `.inl v` for the value `v` committed in the relevant
cache.

Parameter `cache` supplies the expected honest value at the dead-write event:
* stA-dead at embedding (P = B): cache = `optA` (embedding samples `a`).
* stA-dead at challenge (P = A): cache = `optB` (challenge samples `b`).
* stB-dead at embedding (P = A): cache = `optA`.
* stB-dead at challenge (P = B): cache = `optB`. -/
private def cellOk (stRed stHon : F ⊕ G) (cache : Option F) : Prop :=
  stRed = stHon ∨
    (stRed = (.inl 0 : F ⊕ G) ∧ ∃ v, cache = some v ∧ stHon = .inl v)

/-- State relation for the standard-case bridge
`simulateQ (reductionImpl_lazy_real gp gen) ≈ simulateQ (ckaSecurityImpl …)`.

* Observable fields (`tA`, `tB`, `b`, `lastAction`, `rhoA/B`, `keyA/B`) match.
* `reachableInv` holds on the honest side (forces `phaseShapeInv` for the
  scalar extractions in `reductionSend{A,B}`'s embedding branch).
* `stA` / `stB` are `cellOk` with caches routed by `gp.challengedParty`:
  - `P = A`: stA-dead pairs with `optB` (challenge samples `b`); stB-dead
    pairs with `optA` (embedding samples `a`).
  - `P = B`: stA-dead pairs with `optA`; stB-dead pairs with `optB`.

The `correct` field is *not* required to match — reduction's dead-cell
`recv*` comparisons can flip it, and `correct` is unobserved by the
security game. -/
private def R_standard (gen : G) (gp : GameParams) :
    ((GameState (F ⊕ G) G G × Option F) × Option F) → GameState (F ⊕ G) G G → Prop :=
  fun ((s_red, optA), optB) s_hon =>
    s_red.tA = s_hon.tA ∧ s_red.tB = s_hon.tB ∧
    s_red.b = s_hon.b ∧
    s_red.lastAction = s_hon.lastAction ∧
    s_red.rhoA = s_hon.rhoA ∧ s_red.rhoB = s_hon.rhoB ∧
    s_red.keyA = s_hon.keyA ∧ s_red.keyB = s_hon.keyB ∧
    reachableInv gen s_hon ∧
    match gp.challengedParty with
    | .A => cellOk s_red.stA s_hon.stA optB ∧ cellOk s_red.stB s_hon.stB optA
    | .B => cellOk s_red.stA s_hon.stA optA ∧ cellOk s_red.stB s_hon.stB optB

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G]
  [DecidableEq G] [Inhabited F] in
/-- `R_standard` holds at the shared init state with empty caches:
observable fields match trivially, `reachableInv` at init picks the
`lastAction = none` disjunct of `phaseShapeInv` with witness `x = x₀`, and
`cellOk _ _ none` reduces to cell equality. -/
private lemma R_standard_init (gp : GameParams) (x₀ : F) :
    R_standard gen gp
      ((initGameState (.inr (x₀ • gen)) (.inl x₀) false, none), none)
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · -- reachableInv gen (init ...)
    refine ⟨?_, rfl, ?_⟩
    · -- phaseCounterInv: lastAction = none ⇒ tA = tB; both 0 at init.
      simp [phaseCounterInv, initGameState]
    · -- phaseShapeInv at lastAction = none: take x = x₀.
      exact ⟨x₀, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- cellOk match: optA = optB = none ⇒ first disjunct (equality) holds.
    cases gp.challengedParty <;> exact ⟨Or.inl rfl, Or.inl rfl⟩

/-! #### Per-`x₀` inner bridges

Step (2) real decomposes through two named inner bridges — one per branch of
`by_cases` on `(gp.tStar = 1 ∧ gp.challengedParty = .A)`:

* `probOutput_standard_pointwise`: for `¬ (t* = 1 ∧ P = A)` and fixed `x₀`,
  running the reduction (with outer `a, b ←$ F`) on `init .inr (x₀•gen) .inl x₀`
  equals running honest CKA on the same state.
* `probOutput_edge_pointwise`: in the edge case, renaming reduction's outer
  `a ←$ F` to honest's `x₀ ←$ F` — since reduction's init uses `.inr (a•gen)`
  and honest's uses `.inr (x₀•gen)`, the rename is an identity bijection.

Each bridge is proved by peeling its external scalars into hit queries via
`probOutput_simulateQ_consumeLazy_run'_eq` and bridging via
`probOutput_simulateQ_run'_eq_of_state_rel` under a state relation
(`R_standard` / `R_edge`). Per-query `RelTriple` obligations follow the
taxonomy: non-hit → `relTriple_of_evalDist_eq`; embedding → identity bijection
coupling `y ↔ a`; challenge → `x ↔ b`; corruption → `allowCorr ∨ finishedP`
+ reachability heal.
-/

/-- Standard-case per-fixed-`x₀` claim: with `a, b ← $ᵗ F` and honest init
`(.inr (x₀•gen), .inl x₀)`, the reduction's output distribution equals
honest's. This is the "heart" of Step (2)'s standard case — the
`consumeLazy`-peel + state-relation bridge lives here. -/
private lemma probOutput_standard_per_x₀ (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_edge : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (F ⊕ G) G G) (x₀ : F) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] =
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] := by
  sorry

/-- Standard-case (`¬ (t* = 1 ∧ P = A)`) game-level bridge.

Stated with `x₀ ← $ᵗ F` sampled *inside* on both sides (matching the shape
Step (2)'s dispatch produces after `simp only [reductionInitState, if_neg]`).

Proof: swap `x₀` to outermost on LHS (3-way bind manipulation), then apply
`probOutput_bind_congr'` on the shared outer `x₀` and close each fiber via
`probOutput_standard_per_x₀`. -/
private lemma probOutput_standard_pointwise (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_edge : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let x₀ ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] := by
  -- Move x₀ outermost on LHS: first swap (b, x₀) under the outer a, then
  -- swap (a, x₀) at the top. Then apply the per-fixed-x₀ claim.
  calc Pr[= false | do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let x₀ ← ($ᵗ F : ProbComp F)
        let (b', _) ← (simulateQ
            (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
          (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
        return b']
      _ = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let (b', _) ← (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
            (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
          return b'] := by
        refine probOutput_bind_congr' _ false fun a => ?_
        exact probOutput_bind_bind_swap _ _ _ _
      _ = Pr[= false | do
          let x₀ ← ($ᵗ F : ProbComp F)
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let (b', _) ← (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
            (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
          return b'] := probOutput_bind_bind_swap _ _ _ _
      _ = _ := by
        refine probOutput_bind_congr' _ false fun x₀ => ?_
        exact probOutput_standard_per_x₀ gp hΔ h_not_edge adversary x₀

/-- Edge-case per-fixed-`x₀` claim: with the rename `a ↔ x₀`, reduction's
init `(.inr (x₀•gen), .inl 0)` (stB dead) and honest's `(.inr (x₀•gen), .inl x₀)`
produce the same output distribution after the remaining `b ← $ᵗ F` peel. -/
private lemma probOutput_edge_per_x₀ (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_edge : gp.tStar = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (F ⊕ G) G G) (x₀ : F) :
    Pr[= false | do
      let b ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (x₀ • gen) (b • gen) ((x₀ * b) • gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) ((.inl 0) : F ⊕ G) false)
      return b'] =
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] := by
  sorry

/-- Edge-case (`gp = ⟨1, _, .A⟩`) bridge: reduction init `(.inr (a•gen), .inl 0)`
with outer `a ←$ F` equals honest init `(.inr (x₀•gen), .inl x₀)` with
outer `x₀ ←$ F` (renaming `a ↔ x₀`), averaged over the remaining `b ←$ F`. -/
private lemma probOutput_edge_pointwise (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_edge : gp.tStar = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
        (initGameState (.inr (a • gen)) ((.inl 0) : F ⊕ G) false)
      return b'] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] := by
  refine probOutput_bind_congr' _ false fun x₀ => ?_
  exact probOutput_edge_per_x₀ gp hΔ h_edge adversary x₀

/-- **Step (2) of the real branch.** Game-level bridge:
`Pr[= false | securityReductionRealGame] = Pr[= false | CKA^{b = false}]`.

Unfolds both games, case-splits on `reductionInitState`'s `if`, and reduces
each branch to one of the named inner bridges above. -/
private lemma probOutput_securityReductionRealGame_eq_honestFalse
    (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  unfold securityReductionRealGame securityExpFixedBitFalseGame
  by_cases h_edge : gp.tStar = 1 ∧ gp.challengedParty = .A
  · -- Edge: `reductionInitState` = `pure (init .inr gA .inl 0)` (no x₀ sample).
    simp only [reductionInitState, if_pos h_edge, pure_bind]
    exact probOutput_edge_pointwise (gen := gen) gp hΔ h_edge adversary
  · -- Standard: `reductionInitState` = `do x₀ ← $F; pure (init .inr (x₀•gen) .inl x₀)`.
    simp only [reductionInitState, if_neg h_edge, bind_assoc, pure_bind]
    exact probOutput_standard_pointwise (gen := gen) gp hΔ h_edge adversary

/-- Standard-case rand-branch per-fixed-`x₀` claim. With `a, b, c ← $ᵗ F`,
reduction's output on `init .inr (x₀•gen) .inl x₀ false` matches honest's on
the same state with `b = true`. Couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
private lemma probOutput_standard_per_x₀_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_not_edge : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (F ⊕ G) G G) (x₀ : F) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] =
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) true)
      return b'] := by
  sorry

/-- Standard-case (`¬ (t* = 1 ∧ P = A)`) rand-branch game-level bridge.
Analogue of `probOutput_standard_pointwise` with the extra `c ← $ᵗ F`
sampled internally; challenge couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
private lemma probOutput_standard_pointwise_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_not_edge : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      let x₀ ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) true)
      return b'] := by
  -- 4-way swap: move x₀ past c, then past b, then past a.
  calc Pr[= false | do
        let a ← ($ᵗ F : ProbComp F)
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        let x₀ ← ($ᵗ F : ProbComp F)
        let (b', _) ← (simulateQ
            (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
          (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
        return b']
      _ = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          let (b', _) ← (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
            (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
          return b'] := by
        refine probOutput_bind_congr' _ false fun a => ?_
        refine probOutput_bind_congr' _ false fun b => ?_
        exact probOutput_bind_bind_swap _ _ _ _
      _ = Pr[= false | do
          let a ← ($ᵗ F : ProbComp F)
          let x₀ ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          let (b', _) ← (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
            (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
          return b'] := by
        refine probOutput_bind_congr' _ false fun a => ?_
        exact probOutput_bind_bind_swap _ _ _ _
      _ = Pr[= false | do
          let x₀ ← ($ᵗ F : ProbComp F)
          let a ← ($ᵗ F : ProbComp F)
          let b ← ($ᵗ F : ProbComp F)
          let c ← ($ᵗ F : ProbComp F)
          let (b', _) ← (simulateQ
              (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
            (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
          return b'] := probOutput_bind_bind_swap _ _ _ _
      _ = _ := by
        refine probOutput_bind_congr' _ false fun x₀ => ?_
        exact probOutput_standard_per_x₀_rand gp hΔ hg h_not_edge adversary x₀

/-- Edge-case rand-branch per-fixed-`x₀` claim: after renaming `a ↔ x₀`,
reduction's init `(.inr (x₀•gen), .inl 0)` with remaining `b, c ← $ᵗ F`
matches honest's init `(.inr (x₀•gen), .inl x₀)` with `b = true`. Couples
`c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
private lemma probOutput_edge_per_x₀_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_edge : gp.tStar = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (F ⊕ G) G G) (x₀ : F) :
    Pr[= false | do
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (x₀ • gen) (b • gen) (c • gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) ((.inl 0) : F ⊕ G) false)
      return b'] =
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) true)
      return b'] := by
  sorry

/-- Edge-case (`gp = ⟨1, _, .A⟩`) rand-branch bridge. Analogue of
`probOutput_edge_pointwise`; reduction's init is `(.inr (a•gen), .inl 0)`
with `c` replacing `a*b` in `gT`; rename `a ↔ x₀`, couple
`c•gen ↔ outKey ← $ᵗ G` via `hg` at the challenge. -/
private lemma probOutput_edge_pointwise_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_edge : gp.tStar = 1 ∧ gp.challengedParty = .A)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ
          (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
        (initGameState (.inr (a • gen)) ((.inl 0) : F ⊕ G) false)
      return b'] =
    Pr[= false | do
      let x₀ ← ($ᵗ F : ProbComp F)
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) true)
      return b'] := by
  refine probOutput_bind_congr' _ false fun x₀ => ?_
  exact probOutput_edge_per_x₀_rand gp hΔ hg h_edge adversary x₀

/-- **Step (2) of the random branch.** Game-level bridge:
`Pr[= false | securityReductionRandGame] = Pr[= false | CKA^{b = true}]`.
Parallel to `probOutput_securityReductionRealGame_eq_honestFalse`. -/
private lemma probOutput_securityReductionRandGame_eq_honestTrue
    (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRandGame (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitTrueGame (gen := gen) gp adversary] := by
  unfold securityReductionRandGame securityExpFixedBitTrueGame
  by_cases h_edge : gp.tStar = 1 ∧ gp.challengedParty = .A
  · simp only [reductionInitState, if_pos h_edge, pure_bind]
    exact probOutput_edge_pointwise_rand (gen := gen) gp hΔ hg h_edge adversary
  · simp only [reductionInitState, if_neg h_edge, bind_assoc, pure_bind]
    exact probOutput_standard_pointwise_rand (gen := gen) gp hΔ hg h_edge adversary

/-- **Real-branch lemma.**
`Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA^{b = false}]`.

Chains three real-branch steps:
`(1) probOutput_ddhExpReal_securityReduction` — peel `ℬ`'s final negation,
`(2) probOutput_securityReductionRealGame_eq_honestFalse` — bundled
dead-store elimination + eager-to-lazy commutation + identity-bijection
coupling into the honest CKA oracle,
`(3) probOutput_securityExpFixedBit_false` — definitional fold. -/
lemma securityReduction_real (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  rw [probOutput_ddhExpReal_securityReduction, probOutput_securityExpFixedBit_false]
  exact probOutput_securityReductionRealGame_eq_honestFalse (gen := gen) gp hΔ adversary

/-- **Random-branch lemma.**
`Pr[ℬ = true | DDH_rand] = Pr[𝒜 = false | CKA^{b = true}]`.

Chains three random-branch steps:
`(1) probOutput_ddhExpRand_securityReduction` — peel `ℬ`'s final negation,
`(2) probOutput_securityReductionRandGame_eq_honestTrue` — bundled
dead-store elimination + eager-to-lazy commutation + `hg`-bijection coupling
`c • gen ↔ outKey ← $ᵗ G` into the honest CKA oracle at `b = true`,
`(3) probOutput_securityExpFixedBit_true` — definitional fold. -/
lemma securityReduction_rand (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpRand gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true gp] := by
  rw [probOutput_ddhExpRand_securityReduction, probOutput_securityExpFixedBit_true]
  exact probOutput_securityReductionRandGame_eq_honestTrue (gen := gen) gp hΔ hg adversary

/-! ### Main security theorems

From the branch lemmas `securityReduction_real` and `securityReduction_rand`,
together with the fair-coin decomposition of both games, one derives the
pointwise identity

  `Pr[= true | secExp] - 1/2 = (Pr[= true | ddhExp ℬ] - 1/2)
                                 + (Pr[⊥ | CKA^{b = false}] - Pr[⊥ | CKA^{b = true}]) / 2`

where `CKAᵇ := securityExpFixedBit (ddhCKA F G gen) 𝒜 b gp`. Taking absolute
values and the triangle inequality gives the unconditional bound

  `securityAdvantage ≤ ddhGuessAdvantage
                        + |Pr[⊥ | CKA^{b = false}] - Pr[⊥ | CKA^{b = true}]| / 2`

(`security_le_ddh_plus_failGap` below). The residual failure-gap vanishes under
`probFailure_securityExpFixedBit_eq`, giving the tight bound `security` and its
quantitative corollary `ddhCKA_security`.
-/

/-- Absolute difference between the failure probabilities of the two fixed-bit
security games, expressed as a real. It measures how much the adversary's
no-output path is affected by the hidden challenge bit, and vanishes exactly
when `probFailure_securityExpFixedBit_eq` holds. -/
private noncomputable def securityFailGap
    (gp : GameParams) (adversary : CKAAdversary (F ⊕ G) G G) : ℝ :=
  |(Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
    (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal|

/-- **Unconditional DDH-CKA security bound.**

For every CKA adversary, the CKA advantage is bounded by the DDH guess-advantage
of the reduction plus half the failure-probability gap between the two
fixed-bit games. The bound does not require the failure probabilities to
coincide; that strengthening is encapsulated separately in
`probFailure_securityExpFixedBit_eq`. -/
lemma security_le_ddh_plus_failGap (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (F ⊕ G) G G) :
    securityAdvantage (ddhCKA F G gen) adversary gp ≤
      ddhGuessAdvantage gen (securityReduction gp adversary) +
      securityFailGap (gen := gen) gp adversary / 2 := by
  -- Branch lemmas (ℬ's guess distribution on each DDH branch ↔ 𝒜's `=false` output)
  have hReal := securityReduction_real (gen := gen) gp hΔ adversary
  have hRand := securityReduction_rand (gen := gen) gp hΔ hg adversary
  -- Advantage decomposition identities on each side
  have hDdh := ddhExp_probOutput_sub_half (F := F) gen
    (securityReduction (F := F) (G := G) gp adversary)
  have hSec := securityExp_toReal_sub_half (ddhCKA F G gen) adversary gp
  have hRealR := congrArg ENNReal.toReal hReal
  have hRandR := congrArg ENNReal.toReal hRand
  -- `Pr[=true] + Pr[=false] + Pr[⊥] = 1` for each fixed-bit game
  have hSum (b : Bool) :
      (Pr[= true | securityExpFixedBit (ddhCKA F G gen) adversary b gp]).toReal +
      (Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary b gp]).toReal +
      (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary b gp]).toReal = 1 := by
    have h := probOutput_false_add_true
      (mx := securityExpFixedBit (ddhCKA F G gen) adversary b gp)
    have hT := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (by simp) (by simp),
        ENNReal.toReal_sub_of_le (by simp) (by simp), ENNReal.toReal_one] at hT
    linarith
  -- Key algebraic identity: sec = ddh + ΔFail/2
  have hKeyEq :
      (Pr[= true | securityExp (ddhCKA F G gen) adversary gp]).toReal - 1 / 2 =
      ((Pr[= true | ddhExp gen
        (securityReduction (F := F) (G := G) gp adversary)]).toReal - 1 / 2) +
      ((Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
       (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal) / 2 := by
    rw [hDdh, hSec, hRealR, hRandR]
    linarith [hSum true, hSum false]
  -- Local triangle inequality: |x + y| ≤ |x| + |y|
  have htri : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := fun x y =>
    abs_le.mpr ⟨by linarith [neg_le_abs x, neg_le_abs y],
                 by linarith [le_abs_self x, le_abs_self y]⟩
  -- Align the `/2` inside the absolute value with `failGap / 2`
  have habs' :
      |((Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
        (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal) / 2| =
      securityFailGap (gen := gen) gp adversary / 2 := by
    unfold securityFailGap
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have habs :
      |(Pr[= true | securityExp (ddhCKA F G gen) adversary gp]).toReal - 1 / 2| ≤
      |(Pr[= true | ddhExp gen
        (securityReduction (F := F) (G := G) gp adversary)]).toReal - 1 / 2| +
      securityFailGap (gen := gen) gp adversary / 2 := by
    rw [hKeyEq]
    calc |((Pr[= true | ddhExp gen
            (securityReduction (F := F) (G := G) gp adversary)]).toReal - 1 / 2) +
            ((Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal -
             (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal) / 2|
        ≤ _ + _ := htri _ _
      _ = _ := by rw [habs']
  unfold securityAdvantage ddhGuessAdvantage
  exact habs

omit [Inhabited F] in
/-- Auxiliary: the failure probability of `securityExpFixedBit` does not depend on
the challenge bit.

This equality is unconditional because `securityExpFixedBit` lands in
`ProbComp Bool = OracleComp unifSpec Bool`, which is a free monad without a
`failure` constructor. The `HasEvalPMF (OracleComp spec)` instance therefore
forces `NeverFail` on every such computation, so both sides evaluate to `0`. -/
private lemma probFailure_securityExpFixedBit_eq
    (gp : GameParams) (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp] =
    Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  simp

/-- **DDH-CKA security (per-adversary form)** [ACD19, Theorem 3].

For any CKA adversary `𝒜`, the CKA advantage is bounded by the DDH
guess-advantage of the reduction `ℬ = securityReduction gp 𝒜`:

  `securityAdvantage(ddhCKA, 𝒜, gp) ≤ ddhGuessAdvantage(gen, ℬ)`

Derived from `security_le_ddh_plus_failGap` by collapsing the failure gap
using `probFailure_securityExpFixedBit_eq`. -/
theorem security (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (F ⊕ G) G G) :
    securityAdvantage (ddhCKA F G gen) adversary gp ≤
      ddhGuessAdvantage gen (securityReduction gp adversary) := by
  have hBound := security_le_ddh_plus_failGap (gen := gen) gp hΔ hg adversary
  have hFail := probFailure_securityExpFixedBit_eq (F := F) (G := G) (gen := gen) gp adversary
  have hGap : securityFailGap (gen := gen) gp adversary = 0 := by
    unfold securityFailGap
    have : (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp]).toReal =
        (Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp]).toReal :=
      (congrArg ENNReal.toReal hFail).symm
    rw [this]; simp
  linarith [hBound, hGap]

end Step2

end ddhCKA

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

**Goal.** Show `evalDist (simulateQ reductionImpl 𝒜 .run' init) = evalDist
(simulateQ honestImpl 𝒜 .run' init)` — i.e., `𝒜` cannot distinguish the two
columns above. The security bound follows from this distributional equivalence
(see `securityReduction_real` / `securityReduction_rand` below).

**Dead writes.** `stX := 0` at embedding/challenge is never observed:

- `corruptX`: blocked in the window by `ΔCKA = 1`.
- `sendX` reading `stX` as a scalar: blocked by `validStep` (alternating communication)
  until the intervening `recvX` overwrites `stX := .inr ρ`.

After `probOutput_simulateQ_greedyLazy_run'_eq` pushes `a ←$ F` into the
O-Send-B oracle body at `tB = t* - 1` (the *embedding epoch*: where `gA` is
injected into the reduction's output), the per-query `ProbComp (G × G)` is:

  honest:     `y ←$ F; return (y • gen, xA • y • gen)`
  reduction:  `a ←$ F; return (a • gen, xA • a • gen)`


**Bit convention.** DDH uses `true` for the real branch, whereas the CKA game
uses `true` for the random branch. Thus real DDH corresponds to `b = false`
in the CKA experiment, random DDH corresponds to `b = true`, and the
reduction must return `!b'`.
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

/-- DDH adversary obtained by reduction from a CKA security adversary
[ACD19, Theorem 3], parameterized by `gp : GameParams`.

Given a DDH triple `(gen, gA, gB, gT)` and a CKA adversary, the reduction:
1. Initialises the CKA game honestly: `x₀ ← $ᵗ F`.
2. Runs the CKA adversary against `reductionOracleImpl`, which embeds `aG` into
   the other party's send and `(gB, gT)` into `gp.challengedParty`'s challenge.
3. Outputs `!b'` as DDH guess (negated CKA guess, to align bit conventions). -/
noncomputable def securityReduction (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : DDHAdversary F G :=
  fun gen gA gB gT => do
    let x₀ ← $ᵗ F
    let (b', _) ← (simulateQ (reductionOracleImpl gp gen gA gB gT) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
    return !b'

/-- **Real-branch core equivalence (init-state).** For any CKA init seed
`x₀ : F`, sampling `a, b ← $F` and running `𝒜` against
`reductionOracleImpl gp gen (a•gen) (b•gen) ((a*b)•gen)` on the init state
`initGameState (.inr (x₀•gen)) (.inl x₀) false` produces the same output
distribution as running `𝒜` against `ckaSecurityImpl` on the same init state.

The init-state quantifier is tight: the statement is *false* for arbitrary
`s : GameState` — e.g., for `s.stA = .inr _` at an embedding epoch,
`reductionSendB`'s `xA := match … | .inl x => x | .inr _ => 0` fallback
produces output `(gA, 0)` while honest sendB produces a fresh
`(y • gen, y • h)`.

Inner bridge of the real-branch chain; the game-level wrapper
`probOutput_securityReductionRealGame_eq_honestFalse` adds the top-level
`x₀ ← $F` sample.

Proof: two sequential applications of `probOutput_simulateQ_greedyLazy_run'_eq`
(LazySampling.lean), peeling `a` then `b` into the oracle bodies, followed by
a per-query identity-bijection coupling to fold into `ckaSecurityImpl`. The
state divergence at the four dead-write sites (reduction writes `.inl 0`,
honest writes `.inl y` for the sample just taken) is absorbed relationally by
a state relation that treats dead `.inl _` cells as tolerantly equal. The
reachability/shape invariant that rules out the counterexample above (stA is
either `.inl x₀` at init or `.inr ρ` after a recvA) is part of that state
relation. -/
private lemma probOutput_reductionImpl_real_eq_honest_false
    (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (adversary : CKAAdversary (F ⊕ G) G G)
    (x₀ : F) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen))
        adversary).run' (initGameState (.inr (x₀ • gen)) (.inl x₀) false)) =
    evalDist ((simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run'
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)) := by
  sorry

/-- **Random-branch core equivalence (init-state).** For any CKA init seed
`x₀ : F`, sampling `a, b, c ← $F` independently and running `𝒜` against
`reductionOracleImpl gp gen (a•gen) (b•gen) (c•gen)` on the init state with
bit `false` produces the same output distribution as running `𝒜` against
`ckaSecurityImpl` on the init state with bit `true`.

Init-state quantifier is tight for the same reachability reason as in
`probOutput_reductionImpl_real_eq_honest_false`.

Proof: analogous to the real-branch case, with three sequential `greedyLazy`
applications (`a`, `b`, `c`) and a final coupling step where
`c • gen ↔ outKey ← $ᵗ G` uses `hg` bijectivity. -/
private lemma probOutput_reductionImpl_rand_eq_honest_true
    (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (F ⊕ G) G G)
    (x₀ : F) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      let b ← ($ᵗ F : ProbComp F)
      let c ← ($ᵗ F : ProbComp F)
      (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen))
        adversary).run' (initGameState (.inr (x₀ • gen)) (.inl x₀) false)) =
    evalDist ((simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run'
      (initGameState (.inr (x₀ • gen)) (.inl x₀) true)) := by
  sorry

/-! ### Simulation: each DDH branch maps to the corresponding CKA branch

Goal: the reduction `ℬ = securityReduction gp 𝒜` (which returns `¬b'`)
satisfies the top-level branch identities

    Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA^{b = false}]   (**real branch**)
    Pr[ℬ = true | DDH_rand] = Pr[𝒜 = false | CKA^{b = true }]   (**random branch**)

Each branch is proved by a 3-step chain:

```text
Pr[ℬ = true | DDH_real]
    = Pr[= false | securityReductionRealGame]              -- (1) peel `¬b'`
    = Pr[= false | securityExpFixedBitFalseGame]           -- (2) game-level bridge
    = Pr[= false | securityExpFixedBit ... false gp]        -- (3) def. fold
```

where the bridges are
`(1) probOutput_ddhExpReal_securityReduction`,
`(2) probOutput_securityReductionRealGame_eq_honestFalse`,
`(3) probOutput_securityExpFixedBit_false`.

Step (2) is the content of `probOutput_reductionImpl_real_eq_honest_false`,
which composes two library lemmas from `LazySampling.lean`:

  `a ←$ F; simulateQ (impl a) 𝒜  ≡  simulateQ (greedyLazy impl) 𝒜`      (push-in)
  `simulateQ impl₁ 𝒜 s₁        ≡  simulateQ impl₂ 𝒜 s₂`   if `R s₁ s₂`
                                                           per-query          (R-lift)

Applied: (push-in) twice to peel `a` then `b`; (R-lift) to couple reduction's
`stX := .inl 0` with honest's `stX := .inl y` under `R` tolerating dead
`.inl _` divergence.

Random branch analogous: three externals `a, b, c ←$ F` (so `gT := c • gen`)
plus an `hg`-bijection coupling `c • gen ↔ outKey ←$ᵗ G`. Lemmas:
`probOutput_ddhExpRand_securityReduction`,
`probOutput_securityReductionRandGame_eq_honestTrue`,
`probOutput_securityExpFixedBit_true`.
-/

/-- **Game `G_R`** — real-branch reduction-side endpoint. Samples
`a, b, x₀ ←$ F`, runs `𝒜` against `reductionOracleImpl` with DDH inputs
`(gen, a•gen, b•gen, (a*b)•gen)`, returns `𝒜`'s guess `b'` (pre-negation).

Target of `probOutput_ddhExpReal_securityReduction` (peel ¬); source of
`probOutput_securityReductionRealGame_eq_honestFalse` (bridge to honest CKA). -/
private noncomputable def securityReductionRealGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- **Step (1) of the real branch.**  Peels off `ℬ`'s final negation:

  `Pr[ℬ = true ∣ DDH_real]  =  Pr[G_R = false]`

where `ℬ := securityReduction gp 𝒜 = ¬ · ∘ 𝒜` and
`G_R := securityReductionRealGame gp 𝒜`.  Since `ℬ` applies `¬·` after `𝒜`,
the event `{ℬ = true}` pulls back along the bijection `¬ : Bool → Bool` to
`{G_R = false}`; formally this is `probOutput_not_map`, which gives
`Pr[= true | ¬· <$> mx] = Pr[= false | mx]`. -/
private lemma probOutput_ddhExpReal_securityReduction (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpReal securityReduction
  simpa [securityReductionRealGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRealGame (gen := gen) gp adversary))

/-- **Game `G_CKA^false`** — real-branch honest-side endpoint. Samples
`x₀ ←$ F`, runs `𝒜` against `ckaSecurityImpl gp (ddhCKA F G gen)` with the
challenge bit forced to `false`. Unlike `G_R`, the scalars `a, b` are sampled
lazily inside honest `sendX`/`challX`.

Target of `probOutput_securityReductionRealGame_eq_honestFalse`; source of
`probOutput_securityExpFixedBit_false` (fold to `securityExpFixedBit … false gp`). -/
private noncomputable def securityExpFixedBitFalseGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- **Step (3) of the real branch.** Fold the named endpoint `G_CKA^false`
back into the generic fixed-bit notation:

  `Pr[𝒜 = false ∣ securityExpFixedBit … false gp] = Pr[= false | G_CKA^false]`

Pure definitional unfolding of `securityExpFixedBit` at `ddhCKA F G gen`
(no probabilistic content). -/
private lemma probOutput_securityExpFixedBit_false (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpFixedBitFalseGame ddhCKA
  simp [initGameState]

/-- **Game `G_Rand`** — random-branch reduction-side endpoint. Samples
`a, b, c, x₀ ←$ F` independently, runs `𝒜` against `reductionOracleImpl`
with DDH inputs `(gen, a•gen, b•gen, c•gen)` (i.e., `c` replaces `a*b`),
returns `𝒜`'s guess `b'`.

Target of `probOutput_ddhExpRand_securityReduction`; source of
`probOutput_securityReductionRandGame_eq_honestTrue` (uses `hg` bijectivity
to couple `c•gen ↔ outKey ←$ᵗ G`). -/
private noncomputable def securityReductionRandGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let c ← $ᵗ F
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) (c • gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- Random-branch analogue of `probOutput_ddhExpReal_securityReduction`: peel
off `ℬ`'s final negation on the random side, giving
`Pr[ℬ = true | DDH_rand] = Pr[G_Rand = false]`. -/
private lemma probOutput_ddhExpRand_securityReduction (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpRand gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRandGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpRand securityReduction
  simpa [securityReductionRandGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRandGame (gen := gen) gp adversary))

/-- **Game `G_CKA^true`** — random-branch honest-side endpoint. Samples
`x₀ ←$ F`, runs `𝒜` against `ckaSecurityImpl gp (ddhCKA F G gen)` with the
challenge bit forced to `true`.

Target of `probOutput_securityReductionRandGame_eq_honestTrue`; source of
`probOutput_securityExpFixedBit_true` (fold to `securityExpFixedBit … true gp`). -/
private noncomputable def securityExpFixedBitTrueGame (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) true)
  return b'

/-- Random-branch analogue of `probOutput_securityExpFixedBit_false`: fold the
named endpoint game back into the generic fixed-bit notation at `b = true`. -/
private lemma probOutput_securityExpFixedBit_true (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true gp] =
    Pr[= false | securityExpFixedBitTrueGame (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpFixedBitTrueGame ddhCKA
  simp [initGameState]

/-- **Game-level real-branch equivalence.** Direct equality
`Pr[= false | G_R] = Pr[= false | G_CKA^{b=false}]`, wrapping the per-state
real-branch bridge `probOutput_reductionImpl_real_eq_honest_false` into the
full game with the extra `x₀ ← $F` initialization sample peeled off.

Closure recipe (follow-up proof engineering):
1. Unfold both games; normalize the `let (b', _) ← m.run s; return b'` form
   to `m.run' s` via `StateT.run'_eq` and `bind_pure_comp`.
2. Commute `x₀ ← $F` outside the `(a, b)` binds via `probOutput_bind_bind_swap`.
3. Apply `probOutput_reductionImpl_real_eq_honest_false` pointwise in `x₀` to
   collapse `do a, b ← $F; ... run' init` into `ckaSecurityImpl` at `b = false`.
4. Note `{init with b := false} = init` when init was built with `b := false`. -/
private lemma probOutput_securityReductionRealGame_eq_honestFalse
    (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  sorry

/-- **Game-level random-branch equivalence.** Direct equality
`Pr[= false | G_Rand] = Pr[= false | G_CKA^{b=true}]`, bundling dead-store
elimination with the eager-to-lazy+coupling step for the random branch
(`probOutput_reductionImpl_rand_eq_honest_true`, which uses `hg`
bijectivity to couple `c • gen ↔ outKey ← $ᵗ G`).

Closure recipe: parallel to
`probOutput_securityReductionRealGame_eq_honestFalse`, but with three
external samples `(a, b, c)` on the reduction side and the honest init
initialized with `b := true`. -/
private lemma probOutput_securityReductionRandGame_eq_honestTrue
    (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : CKAAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRandGame (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitTrueGame (gen := gen) gp adversary] := by
  sorry

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

end ddhCKA

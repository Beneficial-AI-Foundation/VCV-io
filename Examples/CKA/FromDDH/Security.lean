import Examples.CKA.FromDDH.Common
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Tactics.Common.OracleSum
import VCVio.ProgramLogic.Tactics.Relational
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
general-case init `x₀ ←$ F` with `gA` embedded at the pre-challenge send.

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
open scoped OracleComp.ProgramLogic

-- Internal proofs in this file use the bare `query` identifier in its
-- primitive `OracleQuery spec _` form. Upstream's `HasQuery` refactor
-- (#349) made the bare `query` resolve to `HasQuery.query`; the local
-- notation below restores the primitive resolution within this file.
local notation "query" => OracleSpec.query

namespace ddhCKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open CKAScheme DiffieHellman ckaSecuritySpec

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

/-! ### Cache-aware honest oracles

Mirror images of `reductionSend{A,B}` / `reductionChall{A,B}` that take the
hit-event scalars `a, b : F` as parameters in place of the internal `x ←$ᵗ F`
samples performed by the regular honest CKA oracles. They form the impl-family
fed to `consumeLazy` on the honest side; running `consumeLazy ... honestImpl_lazy`
from the empty cache is distributionally equivalent to running the regular
`ckaSecurityImpl` (bijection coupling between the cached and internal samples).

At non-embedding / non-challenge events these oracles are pointwise equal to
the corresponding regular honest oracles, ensuring the impl-family does not
depend on the cached scalars at non-hit queries. -/

/-- Cache-aware honest sendB oracle. At on-party (P=A) with the embedding
predicate firing, substitutes parameter `a` for `ddhCKA.send`'s internal
`x' ← $ᵗ F`. Otherwise delegates literally to `oracleSendB (ddhCKA F G gen)`,
which makes the off-party dispatch lemma `rfl`-close. -/
private noncomputable def honestSendB_lazy (gp : GameParams) (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tB := state.tB + 1 }
    if validStep state.lastAction .sendB && gp.challengedParty == .A &&
        isOtherSendBeforeChall gp state' then
      match state'.stB with
      | .inr h =>
        let key := a • h
        let ρ := a • gen
        set { state' with
          stB := (.inl a : F ⊕ G), rhoB := some ρ, keyB := some key,
          lastAction := some .sendB }
        return some (ρ, key)
      | .inl _ => pure none
    else
      oracleSendB (ddhCKA F G gen) ()

/-- Cache-aware honest sendA oracle. At on-party (P=B) with the embedding
predicate firing, substitutes parameter `a`. Otherwise delegates literally
to `oracleSendA (ddhCKA F G gen)`. -/
private noncomputable def honestSendA_lazy (gp : GameParams) (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tA := state.tA + 1 }
    if validStep state.lastAction .sendA && gp.challengedParty == .B &&
        isOtherSendBeforeChall gp state' then
      match state'.stA with
      | .inr h =>
        let key := a • h
        let ρ := a • gen
        set { state' with
          stA := (.inl a : F ⊕ G), rhoA := some ρ, keyA := some key,
          lastAction := some .sendA }
        return some (ρ, key)
      | .inl _ => pure none
    else
      oracleSendA (ddhCKA F G gen) ()

/-- Cache-aware honest challA oracle. At on-party (P=A) with the challenge
epoch firing, substitutes parameter `b` for `cka.sendA`'s internal sample.
Otherwise delegates literally to `oracleChallA gp (ddhCKA F G gen)`. -/
private noncomputable def honestChallA_lazy (gp : GameParams) (gen : G) (b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tA := state.tA + 1 }
    if validStep state.lastAction .challA && gp.challengedParty == .A &&
        isChallengeEpoch gp state' then
      match state'.stA with
      | .inr h =>
        let key := b • h
        let ρ := b • gen
        set { state' with
          stA := (.inl b : F ⊕ G), rhoA := some ρ, keyA := some key,
          lastAction := some .challA }
        return some (ρ, key)
      | .inl _ => pure none
    else
      oracleChallA gp (ddhCKA F G gen) ()

/-- Cache-aware honest challB oracle. Symmetric to `honestChallA_lazy`. -/
private noncomputable def honestChallB_lazy (gp : GameParams) (gen : G) (b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    let state' := { state with tB := state.tB + 1 }
    if validStep state.lastAction .challB && gp.challengedParty == .B &&
        isChallengeEpoch gp state' then
      match state'.stB with
      | .inr h =>
        let key := b • h
        let ρ := b • gen
        set { state' with
          stB := (.inl b : F ⊕ G), rhoB := some ρ, keyB := some key,
          lastAction := some .challB }
        return some (ρ, key)
      | .inl _ => pure none
    else
      oracleChallB gp (ddhCKA F G gen) ()

/-- Cache-aware honest oracle stack, parameterized by hit-event scalars `a, b`.
Identical to `ckaSecurityImpl gp (ddhCKA F G gen)` at non-hit queries; at hit
queries (embedding / challenge), uses the parameters in place of internal
samples. `honestImpl_lazy_real gp gen a b` mirrors the shape of
`reductionOracleImpl gp gen (a•gen) (b•gen) ((a*b)•gen)`. -/
private noncomputable def honestImpl_lazy_real (gp : GameParams) (gen : G) (a b : F) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  (oracleUnif (F ⊕ G) G G
    + honestSendA_lazy (F := F) gp gen a
    + oracleRecvA (ddhCKA F G gen)
    + honestSendB_lazy (F := F) gp gen a
    + oracleRecvB (ddhCKA F G gen))
  + honestChallA_lazy (F := F) gp gen b
  + honestChallB_lazy (F := F) gp gen b
  + oracleCorruptA gp (F ⊕ G) G G
  + oracleCorruptB gp (F ⊕ G) G G

/-- Initial CKA game state used by the reduction, case-split on game parameters `gp`.

* **Special case** `gp = ⟨1, _, .A⟩`: `challA` must fire as the first action
  (`validStep none .challA`), so no embedding-send can precede the challenge.
  In this case the reduction identifies `x₀` with `a` by directly injecting
  `gA` into `stA`, skipping the usual `x₀ ← $ᵗ F` sample. The placeholder
  `.inl 0` in `stB` is a dead cell — B's internal key check at subsequent
  `recvB` flips `state.correct`, which is unobserved by the security game.

* **General case**: `x₀ ← $ᵗ F`, `stA := .inr (x₀•gen)`, `stB := .inl x₀`,
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

* **General case** (`gp ≠ ⟨1, _, .A⟩`). Both sides start from
  `(stA, stB) = (x₀•gen, x₀)` with shared outer `x₀ ←$ F`. For each fixed
  `x₀`: push `a, b` into hit queries (embedding + challenge); couple by `R`
  matching all cells except dead writes `stX: 0 ↔ y`, bijected `y ↔ a/b`
  with honest's fresh in-oracle sample.

* **Special case** (`gp = ⟨1, _, .A⟩`). Reduction init `(gA, 0)` vs honest
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

/-! ### Step (2): lazy sampling and state simulation

For each branch:

  securityReductionRealGame  =  securityExpFixedBitFalseGame
  securityReductionRandGame  =  securityExpFixedBitTrueGame.

We have gA,gB,gT where:
- gA = a•gen
- gB = b•gen
- gT = (a·b)•gen or gT = c•gen (where c is random)
where a,b,c are sampled by the DDH experiment eagerly at beginning.

The goal is to show that a,b,c can be equivalently sampled lazily, at the place of use,
so that the experiment is closer to CKA.

1. **Lazy sampling of scalars.**
For
   `I a b := reductionOracleImpl gp gen (a•gen) (b•gen) ((a·b)•gen)`
   (real branch; rand uses `(c•gen)` for `gT` with an extra `c ←$ F`),
we have:
     `do a ← $ᵗ F; b ← $ᵗ F; simulateQ (I a b) 𝒜`
       `=  simulateQ reductionImpl_lazy_real 𝒜`

   where
     `reductionImpl_lazy_real := consumeLazy (hit := hitB gp) (fun b =>
        consumeLazy (hit := hitA gp) (fun a => I a b))`

   defers each sample to the first query where its predicate holds.
   With `P := gp.challengedParty` and `Q := P.other`, two embedding events:

     `send Q`  at `tQ = t* - 1`  embeds `gA = a•gen` into `ρ`
     `chall P` at `tP = t*`      embeds `(gB, gT) = (b•gen, (a·b)•gen)` into `(ρ, key)`

   (Counters are post-increment, after the oracle's `tX++`.) Hit predicates
   select the query tags where samples are needed:

     `hitA i ↔ i ∈ {send Q, chall P}`   -- `a` used at both events
     `hitB i ↔ i = chall P`             -- `b` used only at the challenge

   Off-epoch hits cache the sample without observable effect.

2. **State simulation.**
We define a relation `R_general` between

- the lazy reduction's state `(stateR, a, b)`, and
- the honest CKA state `stateH`

as the conjunction of:

   - **observable equality** — `stateR` and `stateH` agree on
     `tA, tB, b, lastAction, rho{A,B}, key{A,B}`.

   - **placeholder coupling** — for each of `stA, stB`: either both sides
     agree, or the reduction holds the placeholder `0` and honest holds a
     scalar `v ∈ F`, with `v` equal to the value carried in reduction's
     matching `consumeLazy` cache.

   - **reachability** — `reachableInv` (reachable state invariant) holds on `stateH`.

Lemma `probOutput_simulateQ_run'_eq_of_state_rel` reduces the
game-level equivalence to per-query `RelTriple`s: each oracle preserves
`R_general` on its post-state and produces equal observable outputs.
-/

section Step2
variable [Inhabited F]
variable [Fintype G]

omit [Field F] [SampleableType F] [SampleableType G] [DecidableEq G] [Inhabited F] in
private instance ckaSecuritySpec_Fintype :
    (ckaSecuritySpec (F ⊕ G) G G).Fintype := by
  unfold ckaSecuritySpec ckaCorrectnessSpec
  infer_instance

omit [Field F] [SampleableType F] [SampleableType G] [DecidableEq G] [Inhabited F]
  [Fintype G] [Fintype F] in
private instance ckaSecuritySpec_Inhabited :
    (ckaSecuritySpec (F ⊕ G) G G).Inhabited := by
  unfold ckaSecuritySpec ckaCorrectnessSpec
  infer_instance

open OracleComp.ProgramLogic.Relational in
/-- Predicate defining which oracle calls may require embedding of scalar a -/
private def hitA (gp : GameParams) :
    (ckaSecuritySpec (F ⊕ G) G G).Domain → Bool
  | OChallA =>  -- challA
      gp.challengedParty = .A
  | OChallB =>          -- challB
      gp.challengedParty = .B
  | OSendB =>  -- sendB
      gp.challengedParty = .A
  | OSendA =>  -- sendA
      gp.challengedParty = .B
  | _ => false

/-- Predicate defining which oracle calls may require embedding of scalar b -/
private def hitB (gp : GameParams) :
    (ckaSecuritySpec (F ⊕ G) G G).Domain → Bool
  | OChallA =>  -- challA
      gp.challengedParty = .A
  | OChallB =>          -- challB
      gp.challengedParty = .B
  | _ => false

open OracleComp.ProgramLogic.Relational in
/-- Lazy-sampled reduction impl (real branch) -/
private noncomputable def reductionImpl_lazy_real (gp : GameParams) (gen : G) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G)
      (StateT ((GameState (F ⊕ G) G G × Option F) × Option F) ProbComp) :=
  consumeLazy (hit := hitB gp) (implFam := fun b =>
    consumeLazy (hit := hitA gp) (implFam := fun a =>
      reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)))

open OracleComp.ProgramLogic.Relational in
/-- Cache-aware honest oracle stack wrapped with the same `consumeLazy ∘
consumeLazy` shape as `reductionImpl_lazy_real`. Both sides agree on the
cache structure, so per-query `RelTriple` obligations relate states with
*equal* caches — the placeholder/cellOk discrepancy reduces to the
GameState-level coupling at embedding/challenge events.

The bridge `probOutput_lazy_honest_eq` shows running this from the empty
cache is distributionally equivalent to running the regular `ckaSecurityImpl`
(via `probOutput_simulateQ_consumeLazy_run'_eq` plus a bijection coupling
between cached and internal samples). -/
private noncomputable def ckaSecurityImpl_lazy_real (gp : GameParams) (gen : G) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G)
      (StateT ((GameState (F ⊕ G) G G × Option F) × Option F) ProbComp) :=
  consumeLazy (hit := hitB gp) (implFam := fun b =>
    consumeLazy (hit := hitA gp) (implFam := fun a =>
      honestImpl_lazy_real gp gen a b))

omit [Inhabited F] [Fintype G] in
/-- Lemma: At non-hit queries, the reduction's output doesn't depend on `a` -/
private lemma hindepA_real (gp : GameParams) (b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G) (a₁ a₂ : F)
    (h : hitA gp t = false) :
    (reductionOracleImpl gp gen (a₁ • gen) (b • gen) ((a₁ * b) • gen) t).run s =
    (reductionOracleImpl gp gen (a₂ • gen) (b • gen) ((a₂ * b) • gen) t).run s := by
  -- Match on the 9-way nested Sum domain.
  match t with
  | OCorruptB => rfl  -- corruptB: no gA/gB/gT use
  | OCorruptA => rfl  -- corruptA: no gA/gB/gT use
  | OChallB =>  -- challB: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallB, h_cp]
      rfl
    | B =>
      exfalso
      simp [hitA, h_cp] at h
  | OChallA =>  -- challA: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso
      simp [hitA, h_cp] at h
    | B =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallA, h_cp]
      rfl
  | ORecvB => rfl  -- recvB: no gA use
  | OSendB =>  -- sendB: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso
      simp [hitA, h_cp] at h
    | B =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionSendB, h_cp]
      rfl
  | ORecvA => rfl  -- recvA: no gA use
  | OSendA =>  -- sendA: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionSendA, h_cp]
      rfl
    | B =>
      exfalso
      simp [hitA, h_cp] at h
  | OUnif _ => rfl  -- oracleUnif: no gA use

omit [Fintype G] in
/-- Lemma: At non-hit queries, the reduction's output doesn't depend on `b` -/
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
  | OCorruptB => rfl  -- corruptB: no gB/gT use
  | OCorruptA => rfl  -- corruptA: no gB/gT use
  | OChallB =>  -- challB: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallB, hitA, h_cp]
      rfl
    | B =>
      exfalso
      simp [hitB, h_cp] at h
  | OChallA =>  -- challA: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso
      simp [hitB, h_cp] at h
    | B =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp only [reductionOracleImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        reductionChallA, hitA, h_cp]
      rfl
  | ORecvB => rfl  -- recvB
  | OSendB => rfl  -- sendB (uses gA only, not b)
  | ORecvA => rfl  -- recvA
  | OSendA => rfl  -- sendA (uses gA only)
  | OUnif _ => rfl  -- oracleUnif

omit [Inhabited F] [Fintype G] in
/-- Lazy honest impl-family is `a`-independent at non-`hitA` queries.

At non-hit queries, `honestImpl_lazy_real gp gen a b` dispatches to the
regular honest oracle (`oracleUnif`, `oracleRecv{A,B}`, `oracleCorrupt{A,B}`,
or the non-embedding branch of `honestSend{A,B}_lazy`), none of which read
`a`. Mirror of `hindepA_real` for the lazy honest side. -/
private lemma hindepA_lazy_honest (gp : GameParams) (b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G) (a₁ a₂ : F)
    (h : hitA gp t = false) :
    (honestImpl_lazy_real gp gen a₁ b t).run s =
    (honestImpl_lazy_real gp gen a₂ b t).run s := by
  match t with
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>  -- challB: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp only [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallB_lazy, h_cp]
    | B =>
      exfalso; simp [hitA, h_cp] at h
  | OChallA =>  -- challA: gated by P = .A; impl uses b not a
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso; simp [hitA, h_cp] at h
    | B =>
      simp only [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallA_lazy, h_cp]
  | ORecvB => rfl  -- recvB
  | OSendB =>  -- sendB: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso; simp [hitA, h_cp] at h
    | B =>
      simp [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestSendB_lazy, h_cp]
  | ORecvA => rfl  -- recvA
  | OSendA =>  -- sendA: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      simp [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestSendA_lazy, h_cp]
    | B =>
      exfalso; simp [hitA, h_cp] at h
  | OUnif _ => rfl  -- oracleUnif

omit [Fintype G] in
/-- Lazy honest impl wrapped in inner `consumeLazy hitA` is `b`-independent
at non-`hitB` queries. Mirror of `hindepB_real` for the lazy honest side. -/
private lemma hindepB_lazy_honest (gp : GameParams)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G × Option F) (b₁ b₂ : F)
    (h : hitB gp t = false) :
    (OracleComp.ProgramLogic.Relational.consumeLazy (hit := hitA gp)
        (implFam := fun a => honestImpl_lazy_real gp gen a b₁) t).run s =
    (OracleComp.ProgramLogic.Relational.consumeLazy (hit := hitA gp)
        (implFam := fun a => honestImpl_lazy_real gp gen a b₂) t).run s := by
  match t with
  | OCorruptB => rfl
  | OCorruptA => rfl
  | OChallB =>  -- challB: gated by P = .B
    cases h_cp : gp.challengedParty with
    | A =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallB_lazy, hitA, h_cp]
    | B =>
      exfalso; simp [hitB, h_cp] at h
  | OChallA =>  -- challA: gated by P = .A
    cases h_cp : gp.challengedParty with
    | A =>
      exfalso; simp [hitB, h_cp] at h
    | B =>
      unfold OracleComp.ProgramLogic.Relational.consumeLazy
      simp [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        honestChallA_lazy, hitA, h_cp]
  | ORecvB => rfl  -- recvB
  | OSendB => rfl  -- sendB
  | ORecvA => rfl  -- recvA
  | OSendA => rfl  -- sendA
  | OUnif _ => rfl  -- oracleUnif

/-- Per-cell coupling:
- either the cells match, or
- reduction's cell is the placeholder `.inl 0` while honest's cell is `.inl v`
  for the value `v` committed in the relevant cache. -/
private def cellOk (stRed stHon : F ⊕ G) (cache : Option F) : Prop :=
  stRed = stHon ∨
    (stRed = (.inl 0 : F ⊕ G) ∧ ∃ v, cache = some v ∧ stHon = .inl v)

/-- State relation for the general-case bridge.

Both sides share the augmented state `(GameState × Option F) × Option F`
because the lazy honest handler (`ckaSecurityImpl_lazy_real`) wraps the same
`consumeLazy ∘ consumeLazy` shape as the reduction. Cache equality is then
trivially preserved by every step (consumeLazy reads/writes the cache the
same way on both sides regardless of the underlying impl-family). The
non-trivial coupling is on the `GameState` part: observable equality plus
`cellOk` placeholder absorption at embedding events. -/
private def R_general (gen : G) (gp : GameParams) :
    ((GameState (F ⊕ G) G G × Option F) × Option F) →
    ((GameState (F ⊕ G) G G × Option F) × Option F) → Prop :=
  fun ((s_red, optA_r), optB_r) ((s_hon, optA_h), optB_h) =>
    -- caches equal on both sides
    optA_r = optA_h ∧ optB_r = optB_h ∧
    -- observable equality on `GameState`s: tA, tB, b, lastAction, rho{A,B}, key{A,B}
    s_red.tA = s_hon.tA ∧ s_red.tB = s_hon.tB ∧
    s_red.b = s_hon.b ∧
    s_red.lastAction = s_hon.lastAction ∧
    s_red.rhoA = s_hon.rhoA ∧ s_red.rhoB = s_hon.rhoB ∧
    s_red.keyA = s_hon.keyA ∧ s_red.keyB = s_hon.keyB ∧
    -- reachability on honest side: forces `phaseShapeInv` so reduction's
    -- scalar-extraction at the embedding-`send` doesn't take the
    -- `.inr _ => 0` fallback.
    reachableInv gen s_hon ∧
    -- placeholder coupling for stA, stB; cache routing depends on which
    -- party is challenged (P = A: stA ↔ optB, stB ↔ optA; P = B: swapped).
    match gp.challengedParty with
    | .A => cellOk s_red.stA s_hon.stA optB_r ∧ cellOk s_red.stB s_hon.stB optA_r
    | .B => cellOk s_red.stA s_hon.stA optA_r ∧ cellOk s_red.stB s_hon.stB optB_r

omit [Fintype F] [DecidableEq F] [SampleableType F] [SampleableType G]
  [DecidableEq G] [Inhabited F] [Fintype G] in
/-- Lemma: `R_general` holds at the shared init state with empty caches -/
private lemma R_general_init (gp : GameParams) (x₀ : F) :
    R_general gen gp
      ((initGameState (.inr (x₀ • gen)) (.inl x₀) false, none), none)
      ((initGameState (.inr (x₀ • gen)) (.inl x₀) false, none), none) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · -- reachableInv gen (init ...)
    refine ⟨?_, rfl, ?_⟩
    · simp [phaseCounterInv, initGameState]
    · exact ⟨x₀, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases gp.challengedParty <;> exact ⟨Or.inl rfl, Or.inl rfl⟩

/-! #### Inner bridges (pointwise wrappers)

Step (2) real decomposes through two named inner bridges — one per branch of
`by_cases` on `(gp.tStar = 1 ∧ gp.challengedParty = .A)`:

**General case** (`probOutput_general_pointwise`, for `¬ (t* = 1 ∧ P = A)`):
the reduction game with `a, b, x₀ ←$ F` and the honest CKA game with
`x₀ ←$ F`, both starting from the shared init `(.inr (x₀•gen), .inl x₀)`,
have equal output distributions.

**Special case** (`probOutput_special_pointwise`, for `gp = ⟨1, _, .A⟩`):
reduction's `a ←$ F` plays the role of honest's `x₀ ←$ F`; reduction's init
`(.inr (a•gen), .inl 0)` matches honest's `(.inr (x₀•gen), .inl x₀)` under
the rename `a ↔ x₀` (identity bijection on `F`), modulo the placeholder
`stB := .inl 0` (healed by the first `recvB`).
-/

/-! #### Per-oracle `RelTriple` lemmas (Phase C)

For each of the 9 oracles in `ckaSecuritySpec`, prove that `reductionImpl_lazy_real`
and `ckaSecurityImpl` produce equal observable outputs and `R_general`-related
post-states. The closure strategies (per the case recipe in the section docstring)
are:

  `relTriple_real_step_unifSpec`    -- `oracleUnif` is identical on both sides.
  `relTriple_real_step_recvA`       -- `oracleRecvA cka ()` identical on both
  `relTriple_real_step_recvB`         sides; cellOk on stX healed by `recv` writing
                                      `.inr ρ`. State changes only depend on
                                      observable fields of R_general.
  `relTriple_real_step_corruptA`    -- gated by `allowCorr ∨ finishedA/B`; the gate
  `relTriple_real_step_corruptB`      only fires after a prior `recv` overwrites
                                      any dead `.inl 0` placeholder, so cellOk
                                      gives equality at the read time.
  `relTriple_real_step_sendA`       -- two sub-branches: embedding (`P = .B` and
  `relTriple_real_step_sendB`         epoch matches) takes identity coupling on
                                      `y ↔ a` and commits `optA`; non-embedding
                                      runs honest CKA on both sides.
  `relTriple_real_step_challA`      -- two sub-branches: challenge fires (party
  `relTriple_real_step_challB`        matches) takes identity coupling on `x ↔ b`
                                      and commits `optB`; wrong party returns
                                      `pure none` on both sides.

Each stub takes the per-step hypotheses (`gp, hΔ, h_not_special, s_red, s_hon,
hR`) and the `R_general`-preserving `RelTriple` shape. -/

open OracleComp.ProgramLogic.Relational

omit [Fintype G] in
private lemma relTriple_real_step_unifSpec (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_general : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F) (n : unifSpec.Domain)
    (hR : R_general gen gp s_red s_hon) :
    ⟪ (reductionImpl_lazy_real gp gen (OUnif n)).run s_red
    ~ (ckaSecurityImpl_lazy_real gp gen (OUnif n)).run s_hon
    | fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2⟫ := by
  -- Both sides at unifSpec dispatch to `oracleUnif`, which samples uniformly and
  -- preserves state. consumeLazy wrappers on the LHS pass through with hitA=hitB=false.
  -- After unfolding and `show`-coercion, both sides reduce to
  -- `liftM (query n) >>= fun v => pure (v, <respective state>)`.
  unfold reductionImpl_lazy_real
  unfold OracleComp.ProgramLogic.Relational.consumeLazy
  simp only [hitA, hitB, Bool.false_eq_true, ↓reduceIte,
    reductionOracleImpl, QueryImpl.add_apply_inl,
    oracleUnif, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply]
  change OracleComp.ProgramLogic.Relational.RelTriple
    ((liftM (query n) : ProbComp _) >>= fun v => pure (v, s_red))
    ((liftM (query n) : ProbComp _) >>= fun v => pure (v, s_hon)) _
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
  rintro v _ rfl
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, hR⟩


omit [Fintype G] in
private lemma relTriple_real_step_recvA (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
      RelTriple
      ((reductionImpl_lazy_real gp gen ORecvA).run s_red)
      ((ckaSecurityImpl_lazy_real gp gen ORecvA).run s_hon)
      (fun p₁ p₂ => (p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2)) := by

  sorry

omit [Fintype G] in
private lemma relTriple_real_step_recvB (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    -- TODO: comment
    ⟪ (reductionImpl_lazy_real gp gen ORecvB).run s_red
    ~ (ckaSecurityImpl_lazy_real gp gen ORecvB).run s_hon
    | fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2⟫ := by
  -- Both sides at the recvB index dispatch through `+` to `oracleRecvB cka ()`.
  -- LHS additionally wraps via `consumeLazy ∘ consumeLazy` with `hitB = hitA = false`
  -- at recvB; cached scalars `a, b` are read with `getD default` and dead-stored.
  -- The inner `reductionOracleImpl ... recvB_idx = oracleRecvB cka ()` is
  -- a/b-independent (verified by `hindepA_real`, `hindepB_real`).
  --
  -- After reduction:
  --   LHS = (oracleRecvB cka () s_red.1.1).map (fun p => (p.1, ((p.2, optA), optB)))
  --   RHS = oracleRecvB cka () s_hon
  --
  -- `oracleRecvB cka ()` is deterministic. Case-split on:
  --   1. validStep s.lastAction .recvB — equal by R_general.lastAction
  --   2. s.rhoA — equal by R_general.rhoA
  --   3. ddhCKA.recvB s.stB ρ — depends on s.stB; cellOk allows scalar mismatch.
  --      In the placeholder case (s_red.stB = .inl 0, s_hon.stB = .inl x), both
  --      succeed with `stB' := .inr ρ`, restoring cellOk to the matching disjunct.
  --
  -- Post-state observable fields on both sides:
  --   - tA unchanged on both, still equal
  --   - tB := tB+1 on both (in the success branch), still equal
  --   - lastAction := some .recvB on both
  --   - rhoA := none, rhoB unchanged on both
  --   - keyA := none, keyB unchanged on both
  --   - stA unchanged (cellOk preserved)
  --   - stB := .inr ρ on both (cellOk via matching disjunct)
  --   - correct may diverge (different scalar gives different ok); not in R observable
  --
  -- reachableInv s_hon post-recvB: phaseShapeInv at lastAction = .recvB requires
  -- s_hon.stA = .inl y ∧ s_hon.stB = .inr (y•gen), which follows from the prior
  -- phaseShapeInv at .sendA/.challA giving rhoA = some (y•gen).
  sorry

omit [Fintype G] in
private lemma relTriple_real_step_sendA (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    ⟪(reductionImpl_lazy_real gp gen
          OSendA).run s_red
     ~
     (ckaSecurityImpl_lazy_real gp gen
          OSendA).run s_hon
     | fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2⟫ := by
  sorry

omit [Fintype G] in
private lemma relTriple_real_step_sendB (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionImpl_lazy_real gp gen
          OSendB).run s_red)
      ((ckaSecurityImpl_lazy_real gp gen
          OSendB).run s_hon)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2) := by
  sorry

omit [Fintype G] in
private lemma relTriple_real_step_challA (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionImpl_lazy_real gp gen
          OChallA).run s_red)
      ((ckaSecurityImpl_lazy_real gp gen
          OChallA).run s_hon)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2) := by
  -- BLOCKED: per-query RelTriple as stated is unprovable on the right-party
  -- (P = .A) branch because `R_general` does not constrain the lazy caches
  -- (`optA`, `optB`). At a `challA` hit when the cache is populated to e.g.
  -- `optB = some 0`, the LHS uses `b = 0` deterministically while the RHS
  -- samples `x ←$ F` fresh — output distributions differ.
  --
  -- See discussion above: fix by either strengthening `R_general` to encode
  -- "cache populated only by a prior fresh sample whose value also reached
  -- the honest state" (history-dependent), or retargeting this lemma to a
  -- cache-aware honest handler that mirrors the lazy caches and proving a
  -- separate bridge from there to `ckaSecurityImpl`.
  sorry

omit [Fintype G] in
private lemma relTriple_real_step_challB (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionImpl_lazy_real gp gen OChallB).run s_red)
      ((ckaSecurityImpl_lazy_real gp gen OChallB).run s_hon)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2) := by
  sorry

omit [Fintype G] in
private lemma relTriple_real_step_corruptA (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionImpl_lazy_real gp gen OCorruptA).run s_red)
      ((ckaSecurityImpl_lazy_real gp gen OCorruptA).run s_hon)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2) := by
  sorry

omit [Fintype G] in
private lemma relTriple_real_step_corruptB (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionImpl_lazy_real gp gen OCorruptB).run s_red)
      ((ckaSecurityImpl_lazy_real gp gen OCorruptB).run s_hon)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2) := by
  sorry

omit [Fintype G] in
/-- Per-query `RelTriple` for the general-case bridge: at each oracle index
`i`, lazy reduction and honest CKA produce equal observable outputs and
post-states still related by `R_general`. Dispatches to the per-oracle helper
lemmas above. -/
private lemma relTriple_real_step (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
    (i : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s_red : (GameState (F ⊕ G) G G × Option F) × Option F)
    (s_hon : (GameState (F ⊕ G) G G × Option F) × Option F)
    (hR : R_general gen gp s_red s_hon) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((reductionImpl_lazy_real gp gen i).run s_red)
      ((ckaSecurityImpl_lazy_real gp gen i).run s_hon)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_general gen gp p₁.2 p₂.2) := by
  match i with
  | OCorruptB => exact relTriple_real_step_corruptB gp hΔ h_not_special s_red s_hon hR
  | OCorruptA => exact relTriple_real_step_corruptA gp hΔ h_not_special s_red s_hon hR
  | OChallB => exact relTriple_real_step_challB gp hΔ h_not_special s_red s_hon hR
  | OChallA =>
      exact relTriple_real_step_challA gp hΔ h_not_special s_red s_hon hR
  | ORecvB =>
      exact relTriple_real_step_recvB gp hΔ h_not_special s_red s_hon hR
  | OSendB =>
      exact relTriple_real_step_sendB gp hΔ h_not_special s_red s_hon hR
  | ORecvA =>
      exact relTriple_real_step_recvA gp hΔ h_not_special s_red s_hon hR
  | OSendA =>
      exact relTriple_real_step_sendA gp hΔ h_not_special s_red s_hon hR
  | OUnif n =>
      exact relTriple_real_step_unifSpec gp hΔ h_not_special s_red s_hon n hR

/-! ### Bridge: lazy honest cache-aware ↔ regular honest

`ckaSecurityImpl_lazy_real` from the empty cache produces the same output
distribution as the regular `ckaSecurityImpl`. The bridge proof goes via
`relTriple_simulateQ_run'` with a state relation that ignores the cache
slots on the lazy side (caches are just sample-storage with no observable
impact on outputs).

The single per-query `RelTriple` obligation captures, for each oracle:
* **non-hit queries** (recv*, corrupt*, oracleUnif, send/chall at the
  off-party): the lazy cache-aware handler dispatches to the same
  underlying honest oracle as the regular impl. Reflexive coupling.
* **hit queries** (send embedding, challenge): both sides sample uniformly
  from `F` — the lazy side via `consumeLazy`'s sample, the regular side via
  the underlying oracle's internal `x' / x` sample. Identity bijection
  couples them and produces identical outputs.

The auxiliary lemma `evalDist_ckaSecurityImpl_lazy_eq_eager` converts the
cache-aware shape to an eager form with top-level `a, b ← $ᵗ F` samples;
this is not on the critical path of the bridge but useful in its own right
(and serves as a concrete witness that `consumeLazy` peeling works). -/

/-- Auxiliary: peel both consumeLazy wrappers to expose external samples
`a, b ← $ᵗ F` at the top. Two applications of
`probOutput_simulateQ_consumeLazy_run'_eq` using the `hindep` lemmas. Not
strictly needed for the bridge but kept as a useful intermediate. -/
private lemma evalDist_ckaSecurityImpl_lazy_eq_eager
    (gp : GameParams) (adversary : CKAAdversary (F ⊕ G) G G)
    (s : GameState (F ⊕ G) G G) :
    evalDist ((simulateQ (ckaSecurityImpl_lazy_real gp gen) adversary).run' ((s, none), none)) =
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_lazy_real gp gen a b) adversary).run' s) := by
  unfold ckaSecurityImpl_lazy_real
  rw [← OracleComp.ProgramLogic.Relational.probOutput_simulateQ_consumeLazy_run'_eq
        (spec := ckaSecuritySpec (F ⊕ G) G G) (τ := F)
        (implFam := fun b => OracleComp.ProgramLogic.Relational.consumeLazy
          (hit := hitA gp)
          (implFam := fun a => honestImpl_lazy_real gp gen a b))
        (hit := hitB gp)
        (h_indep := fun t s' b₁ b₂ h => hindepB_lazy_honest gp t s' b₁ b₂ h)
        adversary (s, none)]
  refine evalDist_ext fun y => ?_
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  congr 1
  funext b
  congr 1
  have h_inner := OracleComp.ProgramLogic.Relational.probOutput_simulateQ_consumeLazy_run'_eq
        (spec := ckaSecuritySpec (F ⊕ G) G G) (τ := F)
        (implFam := fun a => honestImpl_lazy_real gp gen a b)
        (hit := hitA gp)
        (h_indep := fun t s'' a₁ a₂ h => hindepA_lazy_honest gp b t s'' a₁ a₂ h)
        adversary s
  exact congr_fun (congr_arg DFunLike.coe h_inner.symm) y

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Off-party dispatch: at `P = .A`, `honestSendA_lazy` is pointwise equal
to `oracleSendA (ddhCKA F G gen)`. Used to apply
`evalDist_eager_honest_lazy_eq_step_passthrough` for the `sendA-P=A` case. -/
private lemma honestSendA_lazy_run_eq_at_P_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (a : F) (s : GameState (F ⊕ G) G G) :
    (honestSendA_lazy (F := F) gp gen a ()).run s =
    (oracleSendA (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.B) = false := by simp [h_cp]
  simp [honestSendA_lazy, StateT.run, h_beq]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Off-party dispatch: at `P = .B`, `honestSendB_lazy` is pointwise equal
to `oracleSendB (ddhCKA F G gen)`. -/
private lemma honestSendB_lazy_run_eq_at_P_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (a : F) (s : GameState (F ⊕ G) G G) :
    (honestSendB_lazy (F := F) gp gen a ()).run s =
    (oracleSendB (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.A) = false := by simp [h_cp]
  simp [honestSendB_lazy, StateT.run, h_beq]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Off-party dispatch: at `P = .B`, `honestChallA_lazy` is pointwise equal
to `oracleChallA gp (ddhCKA F G gen)`. -/
private lemma honestChallA_lazy_run_eq_at_P_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (b : F) (s : GameState (F ⊕ G) G G) :
    (honestChallA_lazy (F := F) gp gen b ()).run s =
    (oracleChallA gp (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.A) = false := by simp [h_cp]
  simp [honestChallA_lazy, StateT.run, h_beq]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Off-party dispatch: at `P = .A`, `honestChallB_lazy` is pointwise equal
to `oracleChallB gp (ddhCKA F G gen)`. -/
private lemma honestChallB_lazy_run_eq_at_P_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (b : F) (s : GameState (F ⊕ G) G G) :
    (honestChallB_lazy (F := F) gp gen b ()).run s =
    (oracleChallB gp (ddhCKA F G gen) ()).run s := by
  have h_beq : (gp.challengedParty == CKAParty.B) = false := by simp [h_cp]
  simp [honestChallB_lazy, StateT.run, h_beq]

/-- **Generic StateT helper**: applying `.run s` to `do let state ← get; F state`
reduces to `(F s).run s`. This combines `StateT.run_bind`, `StateT.run_get`, and
`pure_bind` into a single simp-rewrite. Used to make state-conditional reasoning
in lazy oracle proofs tractable. -/
@[simp]
lemma StateT.run_get_bind {σ α : Type _} {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    (f : σ → StateT σ m α) (s : σ) :
    ((get : StateT σ m σ) >>= f).run s = (f s).run s := by
  simp [StateT.run_bind, StateT.run_get]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- **Generic predicate-false dispatch for `sendA`.**

Lazy `sendA` equals eager `oracleSendA` at any state where the
embedding-firing predicate is false. Subsumes both off-party (`P = .A`
makes `(gp.challengedParty == .B) = false`) and post-event (`s.tA + 1 ≠
gp.tStar - 1` makes `isOtherSendBeforeChall (s with tA++) = false`). -/
private lemma honestSendA_lazy_run_eq_when_pred_false
    (gp : GameParams) (a : F) (s : GameState (F ⊕ G) G G)
    (h_pred : (validStep s.lastAction CKAAction.sendA &&
               (gp.challengedParty == CKAParty.B) &&
               isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = false) :
    (honestSendA_lazy (F := F) gp gen a ()).run s =
    (oracleSendA (ddhCKA F G gen) ()).run s := by
  unfold honestSendA_lazy
  show ((get : StateT _ ProbComp _) >>= _).run s = _
  rw [StateT.run_get_bind]
  simp [h_pred]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Symmetric: lazy `sendB` equals eager when the on-party (`P = .A`)
embedding predicate is false. -/
private lemma honestSendB_lazy_run_eq_when_pred_false
    (gp : GameParams) (a : F) (s : GameState (F ⊕ G) G G)
    (h_pred : (validStep s.lastAction CKAAction.sendB &&
               (gp.challengedParty == CKAParty.A) &&
               isOtherSendBeforeChall gp { s with tB := s.tB + 1 }) = false) :
    (honestSendB_lazy (F := F) gp gen a ()).run s =
    (oracleSendB (ddhCKA F G gen) ()).run s := by
  unfold honestSendB_lazy
  show ((get : StateT _ ProbComp _) >>= _).run s = _
  rw [StateT.run_get_bind]
  simp [h_pred]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Lazy `challA` equals eager when the challenge-firing predicate is false. -/
private lemma honestChallA_lazy_run_eq_when_pred_false
    (gp : GameParams) (b : F) (s : GameState (F ⊕ G) G G)
    (h_pred : (validStep s.lastAction CKAAction.challA &&
               (gp.challengedParty == CKAParty.A) &&
               isChallengeEpoch gp { s with tA := s.tA + 1 }) = false) :
    (honestChallA_lazy (F := F) gp gen b ()).run s =
    (oracleChallA gp (ddhCKA F G gen) ()).run s := by
  unfold honestChallA_lazy
  show ((get : StateT _ ProbComp _) >>= _).run s = _
  rw [StateT.run_get_bind]
  simp [h_pred]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- Lazy `challB` equals eager when the challenge-firing predicate is false. -/
private lemma honestChallB_lazy_run_eq_when_pred_false
    (gp : GameParams) (b : F) (s : GameState (F ⊕ G) G G)
    (h_pred : (validStep s.lastAction CKAAction.challB &&
               (gp.challengedParty == CKAParty.B) &&
               isChallengeEpoch gp { s with tB := s.tB + 1 }) = false) :
    (honestChallB_lazy (F := F) gp gen b ()).run s =
    (oracleChallB gp (ddhCKA F G gen) ()).run s := by
  unfold honestChallB_lazy
  show ((get : StateT _ ProbComp _) >>= _).run s = _
  rw [StateT.run_get_bind]
  simp [h_pred]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- **Post-event `a`-independence at `sendA-P=B`.**

At any state `s` satisfying `s.tA + 1 ≠ gp.tStar - 1`, the lazy honest impl
is `a`-independent at `sendA`. -/
private lemma honestSendA_lazy_a_indep_post_event
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (a₁ a₂ : F)
    (s : GameState (F ⊕ G) G G) (h_post : s.tA + 1 ≠ gp.tStar - 1) :
    (honestSendA_lazy (F := F) gp gen a₁ ()).run s =
    (honestSendA_lazy (F := F) gp gen a₂ ()).run s := by
  have h_pred_false :
      (validStep s.lastAction CKAAction.sendA &&
       (gp.challengedParty == CKAParty.B) &&
       isOtherSendBeforeChall gp { s with tA := s.tA + 1 }) = false := by
    have h_o : isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = false := by
      simp only [isOtherSendBeforeChall, GameState.tP, h_cp, CKAParty.other, beq_iff_eq]
      exact decide_eq_false h_post
    simp [h_o]
  rw [honestSendA_lazy_run_eq_when_pred_false gp a₁ s h_pred_false,
      honestSendA_lazy_run_eq_when_pred_false gp a₂ s h_pred_false]

omit [Inhabited F] [Fintype G] in
/-- **Full impl-level `a`-independence at `P = .B`, post-`sendA`-event.**

Lazy honest impl is `a`-independent at every oracle index, given the
state invariant `s.tA + 1 ≠ gp.tStar - 1` (no further sendA embedding
can fire). The non-`hitA` cases follow `hindepA_lazy_honest`; the `hitA`
cases (`sendA`, `challB`) use the predicate-false dispatch and the fact
that `challB` uses parameter `b`, not `a`. -/
private lemma honestImpl_lazy_real_a_indep_post_sendA
    (gp : GameParams) (h_cp : gp.challengedParty = .B) (b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G) (h_post : s.tA + 1 ≠ gp.tStar - 1)
    (a₁ a₂ : F) :
    (honestImpl_lazy_real gp gen a₁ b t).run s =
    (honestImpl_lazy_real gp gen a₂ b t).run s := by
  match t with
  | OCorruptB => rfl  -- corruptB
  | OCorruptA => rfl  -- corruptA
  | OChallB =>  -- challB at h_cp = .B uses parameter b, not a
    simp [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallB_lazy, h_cp]
  | OChallA =>  -- challA at h_cp = .B is off-party
    simp [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestChallA_lazy, h_cp]
  | ORecvB => rfl  -- recvB
  | OSendB =>  -- sendB at h_cp = .B is off-party
    simp [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      honestSendB_lazy, h_cp]
  | ORecvA => rfl  -- recvA
  | OSendA =>  -- sendA: hit at P=B
    show (honestSendA_lazy gp gen a₁ ()).run s = (honestSendA_lazy gp gen a₂ ()).run s
    exact honestSendA_lazy_a_indep_post_event (gen := gen) gp h_cp a₁ a₂ s h_post
  | OUnif _ => rfl  -- oracleUnif

omit [Inhabited F] [Fintype F] [Fintype G] in
/-- Helper: `oracleCorruptB` doesn't modify state. -/
private lemma oracleCorruptB_state_unchanged
    (gp : GameParams) (s : GameState (F ⊕ G) G G) (z) :
    z ∈ support ((oracleCorruptB gp (F ⊕ G) G G ()).run s) → z.2 = s := by
  unfold oracleCorruptB
  rw [StateT.run_get_bind]
  intro hz
  split_ifs at hz <;>
    · simp [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      exact congrArg Prod.snd hz

omit [Inhabited F] [Fintype F] [Fintype G] in
/-- Helper: `oracleCorruptA` doesn't modify state. -/
private lemma oracleCorruptA_state_unchanged
    (gp : GameParams) (s : GameState (F ⊕ G) G G) (z) :
    z ∈ support ((oracleCorruptA gp (F ⊕ G) G G ()).run s) → z.2 = s := by
  unfold oracleCorruptA
  rw [StateT.run_get_bind]
  intro hz
  split_ifs at hz <;>
    · simp [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      exact congrArg Prod.snd hz

omit [Inhabited F] [Fintype G] in
/-- **Per-query `tA`/`tB` monotonicity.**

Every oracle in `honestImpl_lazy_real` either leaves `state.tA` /
`state.tB` unchanged, or increments exactly one of them by `1`. The
two are orthogonal: A-side oracles (`oracleSendA`, `oracleRecvA`,
`oracleChallA`, `honestSendA_lazy`, `honestChallA_lazy`) only touch
`tA`; B-side oracles (`oracleSendB`, `oracleRecvB`, `oracleChallB`,
`honestSendB_lazy`, `honestChallB_lazy`) only touch `tB`. Both
inequalities lift to the simulation level via
`simulateQ_run_preservesInv` and underpin post-event `a`/`b`-
independence arguments.

Proof outline (per oracle case):
* `oracleUnif`, `oracleCorruptA`, `oracleCorruptB`: state unchanged
  (read-only or pure lift).
* A-side oracles: `tA` unchanged or `tA + 1`; `tB` unchanged.
* B-side oracles: `tB` unchanged or `tB + 1`; `tA` unchanged. -/
private lemma honestImpl_lazy_real_t_monotone
    (gp : GameParams) (a b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G)
    (z : (ckaSecuritySpec (F ⊕ G) G G).Range t × GameState (F ⊕ G) G G)
    (hz : z ∈ support ((honestImpl_lazy_real gp gen a b t).run s)) :
    s.tA ≤ z.2.tA ∧ s.tB ≤ z.2.tB := by
  match t with
  | OCorruptB =>
    -- oracleCorruptB: state unchanged
    simp only [honestImpl_lazy_real, QueryImpl.add_apply_inr] at hz
    have h_eq := oracleCorruptB_state_unchanged gp s z hz
    rw [h_eq]
    exact ⟨le_refl _, le_refl _⟩
  | OCorruptA =>
    -- oracleCorruptA: state unchanged
    simp only [honestImpl_lazy_real, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] at hz
    have h_eq := oracleCorruptA_state_unchanged gp s z hz
    rw [h_eq]
    exact ⟨le_refl _, le_refl _⟩
  | _ =>
    -- TODO: remaining 7 cases (per-oracle unfold + StateT.run normalization +
    -- case-split on validStep / state.stX → state unchanged, tA += 1, or tB += 1).
    -- Mechanical but verbose; deferred while the higher-level wiring proceeds.
    sorry

omit [Inhabited F] [Fintype G] in
/-- At `P = .B` and `gp.tStar - 1 ≤ s.tA` (post-`sendA`-firing state), the
lazy honest simulation is `a`-independent. Lifts the per-query a-indep via
`relTriple_simulateQ_run_of_impl_eq_preservesInv` + `tA` monotonicity. -/
private lemma simulateQ_honest_lazy_a_indep_post_sendA
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (h_tStar : 1 ≤ gp.tStar) (b : F)
    (adv : OracleComp (ckaSecuritySpec (F ⊕ G) G G) Bool)
    (s : GameState (F ⊕ G) G G) (h_post : gp.tStar - 1 ≤ s.tA) (a₁ a₂ : F) :
    evalDist ((simulateQ (honestImpl_lazy_real gp gen a₁ b) adv).run s) =
    evalDist ((simulateQ (honestImpl_lazy_real gp gen a₂ b) adv).run s) := by
  have h_inv_imp : ∀ s' : GameState (F ⊕ G) G G,
      gp.tStar - 1 ≤ s'.tA → s'.tA + 1 ≠ gp.tStar - 1 := by
    intro s' h
    omega
  have hrel := OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run_of_impl_eq_preservesInv
    (impl₁ := honestImpl_lazy_real gp gen a₁ b)
    (impl₂ := honestImpl_lazy_real gp gen a₂ b)
    (Inv := fun s' : GameState (F ⊕ G) G G => gp.tStar - 1 ≤ s'.tA)
    (oa := adv)
    (himpl_eq := fun t s' h_pre =>
      honestImpl_lazy_real_a_indep_post_sendA (gen := gen) gp h_cp b t s'
        (h_inv_imp s' h_pre) a₁ a₂)
    (hpres₂ := fun t s' h_pre z hz =>
      h_pre.trans (honestImpl_lazy_real_t_monotone (gen := gen) gp a₂ b t s' z hz).1)
    s h_post
  exact OracleComp.ProgramLogic.Relational.evalDist_eq_of_relTriple_eqRel
    (OracleComp.ProgramLogic.Relational.relTriple_post_mono hrel
      (fun _ _ hp => hp.1))

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- At `P = .B`, pre-sampling `a ← $ᵗ F` for `honestSendA_lazy` yields the same
distribution as `oracleSendA`'s internal sample. -/
private lemma evalDist_marginalized_honestSendA_lazy_eq_oracleSendA_at_P_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (s : GameState (F ⊕ G) G G) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      (honestSendA_lazy (F := F) gp gen a ()).run s) =
    evalDist ((oracleSendA (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
  -- Strategy: case-split on whether the impl call uses parameter `a`.
  -- Outside the firing case, lazy = eager pointwise (a unused).
  -- In the firing case, lazy uses `a`, eager samples `x` — bijection.
  by_cases h_fire :
      validStep s.lastAction CKAAction.sendA = true ∧
      isOtherSendBeforeChall gp { s with tA := s.tA + 1 } = true ∧
      ∃ h : G, s.stA = .inr h
  · -- Firing case: bijection
    obtain ⟨h_v, h_o, h, h_stA⟩ := h_fire
    rw [h_stA] at h_o
    have h_eq : (do let a ← ($ᵗ F : ProbComp F)
                    (honestSendA_lazy (F := F) gp gen a ()).run s) =
                ((oracleSendA (ddhCKA F G gen) ()).run s) := by
      simp [honestSendA_lazy, oracleSendA, StateT.run_bind, StateT.run_get,
        StateT.lift, pure_bind, bind_pure_comp,
        h_v, h_beq, h_stA, h_o, ddhCKA, ddhCKA.send]
    rw [h_eq]
  · -- Non-firing case: lazy delegates to eager pointwise (a unused).
    have h_lazy_eq_eager : ∀ a : F,
        (honestSendA_lazy (F := F) gp gen a ()).run s =
        (oracleSendA (ddhCKA F G gen) ()).run s := by
      intro a
      cases h_v : validStep s.lastAction CKAAction.sendA with
      | false =>
        simp [honestSendA_lazy, oracleSendA, StateT.run_bind, StateT.run_get,
          StateT.lift, pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        -- The key observation: in honestSendA_lazy at validStep=true, the if-condition
        -- only depends on `state'.stA = s.stA` via OtherSendBeforeChall (which depends
        -- on tA only, NOT on stA). So we can split on stA and OtherSend without
        -- worrying about state-rewriting.
        cases h_o : isOtherSendBeforeChall gp { s with tA := s.tA + 1 } with
        | false =>
          -- !OtherSend: lazy delegates to else (oracleSendA cka ()). Eager runs same.
          simp [honestSendA_lazy, oracleSendA, StateT.run_bind, StateT.run_get,
            StateT.lift, pure_bind, h_v, h_beq, h_o, ddhCKA, ddhCKA.send]
        | true =>
          cases h_stA : s.stA with
          | inl x =>
            -- Lazy: match .inl _ → pure none. Eager via ddhCKA.send .inl _ = pure none.
            -- Note: the goal has the embedding's if-condition with `state'.stA = .inl x`;
            -- since `isOtherSendBeforeChall` only reads tA (not stA), it agrees with `h_o`.
            have h_o' : isOtherSendBeforeChall gp
                { s with stA := (.inl x : F ⊕ G), tA := s.tA + 1 } = true := by
              simp only [isOtherSendBeforeChall] at h_o ⊢
              convert h_o using 2
            simp [honestSendA_lazy, oracleSendA, StateT.run_bind, StateT.run_get,
              StateT.lift, pure_bind, h_v, h_beq, h_o', h_stA, ddhCKA, ddhCKA.send]
          | inr h =>
            -- Contradicts h_fire (which says NOT all of validStep ∧ OtherSend ∧ stA=.inr).
            push_neg at h_fire
            exact absurd h_stA (h_fire h_v h_o h)
    have h_bind_eq :
        (do let a ← ($ᵗ F : ProbComp F)
            (honestSendA_lazy (F := F) gp gen a ()).run s) =
        (do let _a ← ($ᵗ F : ProbComp F)
            (oracleSendA (ddhCKA F G gen) ()).run s) := by
      congr 1
      funext a
      exact h_lazy_eq_eager a
    refine evalDist_ext fun y => ?_
    rw [h_bind_eq, probOutput_bind_const]
    simp [probFailure_uniformSample]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- **On-party bijection helper for `sendB` at `P = .A`.**

Symmetric mirror of `evalDist_marginalized_honestSendA_lazy_eq_oracleSendA_at_P_B`
with party A as the embedding-fires party. -/
private lemma evalDist_marginalized_honestSendB_lazy_eq_oracleSendB_at_P_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (s : GameState (F ⊕ G) G G) :
    evalDist (do
      let a ← ($ᵗ F : ProbComp F)
      (honestSendB_lazy (F := F) gp gen a ()).run s) =
    evalDist ((oracleSendB (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
  by_cases h_fire :
      validStep s.lastAction CKAAction.sendB = true ∧
      isOtherSendBeforeChall gp { s with tB := s.tB + 1 } = true ∧
      ∃ h : G, s.stB = .inr h
  · obtain ⟨h_v, h_o, h, h_stB⟩ := h_fire
    rw [h_stB] at h_o
    have h_eq : (do let a ← ($ᵗ F : ProbComp F)
                    (honestSendB_lazy (F := F) gp gen a ()).run s) =
                ((oracleSendB (ddhCKA F G gen) ()).run s) := by
      simp [honestSendB_lazy, oracleSendB, StateT.run_bind, StateT.run_get,
        StateT.lift, pure_bind, bind_pure_comp,
        h_v, h_beq, h_stB, h_o, ddhCKA, ddhCKA.send]
    rw [h_eq]
  · have h_lazy_eq_eager : ∀ a : F,
        (honestSendB_lazy (F := F) gp gen a ()).run s =
        (oracleSendB (ddhCKA F G gen) ()).run s := by
      intro a
      cases h_v : validStep s.lastAction CKAAction.sendB with
      | false =>
        simp [honestSendB_lazy, oracleSendB, StateT.run_bind, StateT.run_get,
          StateT.lift, pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        cases h_o : isOtherSendBeforeChall gp { s with tB := s.tB + 1 } with
        | false =>
          simp [honestSendB_lazy, oracleSendB, StateT.run_bind, StateT.run_get,
            StateT.lift, pure_bind, h_v, h_beq, h_o, ddhCKA, ddhCKA.send]
        | true =>
          cases h_stB : s.stB with
          | inl x =>
            have h_o' : isOtherSendBeforeChall gp
                { s with stB := (.inl x : F ⊕ G), tB := s.tB + 1 } = true := by
              simp only [isOtherSendBeforeChall] at h_o ⊢
              convert h_o using 2
            simp [honestSendB_lazy, oracleSendB, StateT.run_bind, StateT.run_get,
              StateT.lift, pure_bind, h_v, h_beq, h_o', h_stB, ddhCKA, ddhCKA.send]
          | inr h =>
            push_neg at h_fire
            exact absurd h_stB (h_fire h_v h_o h)
    have h_bind_eq :
        (do let a ← ($ᵗ F : ProbComp F)
            (honestSendB_lazy (F := F) gp gen a ()).run s) =
        (do let _a ← ($ᵗ F : ProbComp F)
            (oracleSendB (ddhCKA F G gen) ()).run s) := by
      congr 1
      funext a
      exact h_lazy_eq_eager a
    refine evalDist_ext fun y => ?_
    rw [h_bind_eq, probOutput_bind_const]
    simp [probFailure_uniformSample]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- **On-party bijection helper for `challA` at `P = .A`, `s.b = false`.**

At the challenge-firing state, lazy uses parameter `b` directly to produce
`(some (b•gen, b•h), state with stA := .inl b)`. Eager (oracleChallA at
`gp.challengedParty == .A` and `isChallengeEpoch`) runs `cka.sendA` (which
samples `x ← $ᵗ F`) and then `outKey ← if s.b then $I else pure key`. With
`s.b = false`, `outKey = key`, so eager returns
`(some (x•gen, x•h), state with stA := .inl x)` — matching by `b ↔ x`.

Without the `s.b = false` hypothesis, the eager would sample a fresh `outKey`
at `s.b = true` while the lazy returns the deterministic `key`; the bridge
would fail. The `s.b = false` invariant is preserved across all reachable
states (no oracle modifies `state.b`) starting from `initGameState … false`. -/
private lemma evalDist_marginalized_honestChallA_lazy_eq_oracleChallA_at_P_A
    (gp : GameParams) (h_cp : gp.challengedParty = .A)
    (s : GameState (F ⊕ G) G G) (h_b : s.b = false) :
    evalDist (do
      let b' ← ($ᵗ F : ProbComp F)
      (honestChallA_lazy (F := F) gp gen b' ()).run s) =
    evalDist ((oracleChallA gp (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.A) = true := by simp [h_cp]
  by_cases h_fire :
      validStep s.lastAction CKAAction.challA = true ∧
      isChallengeEpoch gp { s with tA := s.tA + 1 } = true ∧
      ∃ h : G, s.stA = .inr h
  · obtain ⟨h_v, h_e, h, h_stA⟩ := h_fire
    rw [h_stA, h_b] at h_e
    have h_eq : (do let b' ← ($ᵗ F : ProbComp F)
                    (honestChallA_lazy (F := F) gp gen b' ()).run s) =
                ((oracleChallA gp (ddhCKA F G gen) ()).run s) := by
      simp [honestChallA_lazy, oracleChallA, StateT.run_bind, StateT.run_get,
        StateT.lift, pure_bind, bind_pure_comp,
        h_v, h_beq, h_stA, h_e, h_b, ddhCKA, ddhCKA.send]
    rw [h_eq]
  · have h_lazy_eq_eager : ∀ b' : F,
        (honestChallA_lazy (F := F) gp gen b' ()).run s =
        (oracleChallA gp (ddhCKA F G gen) ()).run s := by
      intro b'
      cases h_v : validStep s.lastAction CKAAction.challA with
      | false =>
        simp [honestChallA_lazy, oracleChallA, StateT.run_bind, StateT.run_get,
          StateT.lift, pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        cases h_e : isChallengeEpoch gp { s with tA := s.tA + 1 } with
        | false =>
          simp [honestChallA_lazy, oracleChallA, StateT.run_bind, StateT.run_get,
            StateT.lift, pure_bind, h_v, h_beq, h_e, ddhCKA, ddhCKA.send]
        | true =>
          cases h_stA : s.stA with
          | inl x =>
            have h_e' : isChallengeEpoch gp
                { s with stA := (.inl x : F ⊕ G), b := false,
                         tA := s.tA + 1 } = true := by
              simp only [isChallengeEpoch] at h_e ⊢
              convert h_e using 2
            simp [honestChallA_lazy, oracleChallA, StateT.run_bind, StateT.run_get,
              StateT.lift, pure_bind, h_v, h_beq, h_e', h_stA, h_b, ddhCKA, ddhCKA.send]
          | inr h =>
            push_neg at h_fire
            exact absurd h_stA (h_fire h_v h_e h)
    have h_bind_eq :
        (do let b' ← ($ᵗ F : ProbComp F)
            (honestChallA_lazy (F := F) gp gen b' ()).run s) =
        (do let _b' ← ($ᵗ F : ProbComp F)
            (oracleChallA gp (ddhCKA F G gen) ()).run s) := by
      congr 1
      funext b'
      exact h_lazy_eq_eager b'
    refine evalDist_ext fun y => ?_
    rw [h_bind_eq, probOutput_bind_const]
    simp [probFailure_uniformSample]

omit [Inhabited F] [Fintype G] [DecidableEq G] in
/-- **On-party bijection helper for `challB` at `P = .B`, `s.b = false`.**

Symmetric mirror of `evalDist_marginalized_honestChallA_lazy_eq_oracleChallA_at_P_A`. -/
private lemma evalDist_marginalized_honestChallB_lazy_eq_oracleChallB_at_P_B
    (gp : GameParams) (h_cp : gp.challengedParty = .B)
    (s : GameState (F ⊕ G) G G) (h_b : s.b = false) :
    evalDist (do
      let b' ← ($ᵗ F : ProbComp F)
      (honestChallB_lazy (F := F) gp gen b' ()).run s) =
    evalDist ((oracleChallB gp (ddhCKA F G gen) ()).run s) := by
  have h_beq : (gp.challengedParty == CKAParty.B) = true := by simp [h_cp]
  by_cases h_fire :
      validStep s.lastAction CKAAction.challB = true ∧
      isChallengeEpoch gp { s with tB := s.tB + 1 } = true ∧
      ∃ h : G, s.stB = .inr h
  · obtain ⟨h_v, h_e, h, h_stB⟩ := h_fire
    rw [h_stB, h_b] at h_e
    have h_eq : (do let b' ← ($ᵗ F : ProbComp F)
                    (honestChallB_lazy (F := F) gp gen b' ()).run s) =
                ((oracleChallB gp (ddhCKA F G gen) ()).run s) := by
      simp [honestChallB_lazy, oracleChallB, StateT.run_bind, StateT.run_get,
        StateT.lift, pure_bind, bind_pure_comp,
        h_v, h_beq, h_stB, h_e, h_b, ddhCKA, ddhCKA.send]
    rw [h_eq]
  · have h_lazy_eq_eager : ∀ b' : F,
        (honestChallB_lazy (F := F) gp gen b' ()).run s =
        (oracleChallB gp (ddhCKA F G gen) ()).run s := by
      intro b'
      cases h_v : validStep s.lastAction CKAAction.challB with
      | false =>
        simp [honestChallB_lazy, oracleChallB, StateT.run_bind, StateT.run_get,
          StateT.lift, pure_bind, h_v, h_beq, ddhCKA]
      | true =>
        cases h_e : isChallengeEpoch gp { s with tB := s.tB + 1 } with
        | false =>
          simp [honestChallB_lazy, oracleChallB, StateT.run_bind, StateT.run_get,
            StateT.lift, pure_bind, h_v, h_beq, h_e, ddhCKA, ddhCKA.send]
        | true =>
          cases h_stB : s.stB with
          | inl x =>
            have h_e' : isChallengeEpoch gp
                { s with stB := (.inl x : F ⊕ G), b := false,
                         tB := s.tB + 1 } = true := by
              simp only [isChallengeEpoch] at h_e ⊢
              convert h_e using 2
            simp [honestChallB_lazy, oracleChallB, StateT.run_bind, StateT.run_get,
              StateT.lift, pure_bind, h_v, h_beq, h_e', h_stB, h_b, ddhCKA, ddhCKA.send]
          | inr h =>
            push_neg at h_fire
            exact absurd h_stB (h_fire h_v h_e h)
    have h_bind_eq :
        (do let b' ← ($ᵗ F : ProbComp F)
            (honestChallB_lazy (F := F) gp gen b' ()).run s) =
        (do let _b' ← ($ᵗ F : ProbComp F)
            (oracleChallB gp (ddhCKA F G gen) ()).run s) := by
      congr 1
      funext b'
      exact h_lazy_eq_eager b'
    refine evalDist_ext fun y => ?_
    rw [h_bind_eq, probOutput_bind_const]
    simp [probFailure_uniformSample]

omit [Inhabited F] [Fintype G] in
/-- **Non-divergence step lemma** for `evalDist_eager_honest_lazy_eq`.

At an oracle index `t` where the lazy and eager implementations agree
pointwise (`(honestImpl_lazy_real gp gen a b t).run s = (ckaSecurityImpl gp
(ddhCKA F G gen) t).run s` for all `a, b`), the per-query bridge step is just
a Fubini swap of the external samples `(b, a)` past the impl call followed
by the inductive hypothesis on the continuation.

Used for the 5 non-divergence cases (unifSpec, recvA, recvB, corruptA,
corruptB) of `evalDist_eager_honest_lazy_eq`'s `query_bind` case. -/
private lemma evalDist_eager_honest_lazy_eq_step_passthrough
    (gp : GameParams) (s : GameState (F ⊕ G) G G)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (k : (ckaSecuritySpec (F ⊕ G) G G).Range t →
         OracleComp (ckaSecuritySpec (F ⊕ G) G G) Bool)
    (h_impl_eq : ∀ (a b : F),
      (honestImpl_lazy_real gp gen a b t).run s =
      (ckaSecurityImpl gp (ddhCKA F G gen) t).run s)
    (h_ih : ∀ (u : (ckaSecuritySpec (F ⊕ G) G G).Range t)
            (s' : GameState (F ⊕ G) G G),
      evalDist (do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        (simulateQ (honestImpl_lazy_real gp gen a b) (k u)).run' s') =
      evalDist ((simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) (k u)).run' s')) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_lazy_real gp gen a b) (query t >>= k)).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) (query t >>= k)).run' s) := by
  apply evalDist_ext; intro y
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
    OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
  -- Step 1: align inner impl call.
  have eq1 : Pr[= y | do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        let p ← (honestImpl_lazy_real gp gen a b t).run s
        Prod.fst <$> (simulateQ (honestImpl_lazy_real gp gen a b) (k p.1)).run p.2] =
      Pr[= y | do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        let p ← (ckaSecurityImpl gp (ddhCKA F G gen) t).run s
        Prod.fst <$> (simulateQ (honestImpl_lazy_real gp gen a b) (k p.1)).run p.2] := by
    refine probOutput_bind_congr' _ y fun b => ?_
    refine probOutput_bind_congr' _ y fun a => ?_
    rw [h_impl_eq a b]
  rw [eq1]
  -- Step 2a: swap `a ← $F` past `p ← impl.run s` (under outer `b`).
  have eq2 : Pr[= y | do
        let b ← ($ᵗ F : ProbComp F)
        let a ← ($ᵗ F : ProbComp F)
        let p ← (ckaSecurityImpl gp (ddhCKA F G gen) t).run s
        Prod.fst <$> (simulateQ (honestImpl_lazy_real gp gen a b) (k p.1)).run p.2] =
      Pr[= y | do
        let b ← ($ᵗ F : ProbComp F)
        let p ← (ckaSecurityImpl gp (ddhCKA F G gen) t).run s
        let a ← ($ᵗ F : ProbComp F)
        Prod.fst <$> (simulateQ (honestImpl_lazy_real gp gen a b) (k p.1)).run p.2] := by
    refine probOutput_bind_congr' _ y fun b => ?_
    exact probOutput_bind_bind_swap (mx := ($ᵗ F : ProbComp F))
      (my := (ckaSecurityImpl gp (ddhCKA F G gen) t).run s)
      (f := fun a p => Prod.fst <$>
        (simulateQ (honestImpl_lazy_real gp gen a b) (k p.1)).run p.2) (z := y)
  rw [eq2]
  -- Step 2b: swap `b ← $F` past `p ← impl.run s`.
  rw [probOutput_bind_bind_swap (mx := ($ᵗ F : ProbComp F))
      (my := (ckaSecurityImpl gp (ddhCKA F G gen) t).run s)
      (f := fun b p => do
        let a ← ($ᵗ F : ProbComp F)
        Prod.fst <$> (simulateQ (honestImpl_lazy_real gp gen a b) (k p.1)).run p.2) (z := y)]
  -- Step 3: apply IH pointwise.
  refine probOutput_bind_congr' _ y fun p => ?_
  have hi := h_ih p.1 p.2
  simp only [StateT.run'_eq] at hi
  exact congrFun (congrArg DFunLike.coe hi) y

omit [Fintype G] in
/-- **Step 2 of the bridge** — the substantive content:

  `do b, a ← $ᵗ F; simulate (honestImpl_lazy_real a b) adv .run' s
   ≡ simulate ckaSecurityImpl adv .run' s`

External samples `a, b` fed into `honestImpl_lazy_real` (which substitutes
them for the internal `x', x` samples at the embedding / challenge events)
are distributionally equivalent to the regular honest game where those
internal samples happen inside the oracles.

Proof technique: induction on `adv : OracleComp ckaSecuritySpec _` via
`OracleComp.inductionOn`:
* `pure x`: both sides reduce to `pure (x, s)`; samples `a, b` are unused.
* `query t >>= k` (case `t`):
  * **Non-divergence queries** (most): `honestImpl_lazy_real a b t = ckaSecurityImpl t`
    pointwise (impl-family is `(a, b)`-independent at non-hit queries).
    Bind-swap external samples past the query (Fubini), apply IH on `k u`.
  * **Embedding queries** (`sendB-P=A`, `sendA-P=B`): bijection on `a ↔ x'`
    via `probOutput_bind_bijective_uniform_cross` with `f = id : F → F`.
    Post-event: committed value flows through state on both sides
    (`stX = .inl a` on LHS via cache, `stX = .inl x'` on RHS via internal
    sample); by coupling `a = x'` they match.
  * **Challenge queries** (`challA-P=A`, `challB-P=B`): bijection on `b ↔ x`,
    same pattern as embedding.

This replaces the broken per-query `relTriple_simulateQ_run'` approach,
which can't capture the cross-event sample correspondence (e.g., `a`
sampled by consumeLazy at a prior `challA-P=A` event but consumed at a
later `sendB-P=A-embedding` event).

**On-party bijection roadmap** (sendA-P=B / sendB-P=A / challA-P=A /
challB-P=B). At an on-party query, the lazy impl uses parameter `a` (or
`b`) directly when the embedding/challenge fires; the eager impl samples
a fresh `x ← $ᵗ F`. The proof strategy:

1. After `simp only [simulateQ_bind, simulateQ_query, …, StateT.run'_eq,
   StateT.run_bind, map_bind]`, expose the impl call inside a `>>= fun p
   => fst <$> (simulateQ … (k p.1)).run p.2`.
2. `refine probOutput_bind_congr' _ y fun b => ?_` to fix the outer `b`
   sample (independent of the embedding event for `a`-cases; symmetric
   for `b`-cases).
3. Split at the impl call: case-split on `validStep`, on `state.stA`
   (or `stB`), and on `isOtherSendBeforeChall` (or `isChallengeEpoch`).
4. In the embedding-fires sub-case (`validStep ∧ stA = .inr h ∧
   OtherSendBeforeChall`), apply `probOutput_bind_bijective_uniform_cross`
   with `f = (id : F → F)` to replace `a ← $ᵗ F; <use a>` on LHS with
   `x ← $ᵗ F; <use x>` on RHS.
5. After bijection, post-event states match (`stA = .inl a` ↔ `stA = .inl
   x` under `a := x`). The lazy impl is then `a`-independent for the
   continuation (since post-embedding `state.stA = .inl _`, future hitA
   queries return `pure none` regardless of the parameter).
6. Use the `a`-independence to add a vacuous `a' ← $ᵗ F` to the LHS,
   then apply IH on `(k p.1)` and `p.2`.

Estimated size: ~150–250 lines per on-party case. The bijection itself
is straightforward (id bijection); the bookkeeping for state-conditional
case splits and post-event a-independence is the bulk. -/
private lemma evalDist_eager_honest_lazy_eq
    (gp : GameParams) (s : GameState (F ⊕ G) G G)
    (adversary : OracleComp (ckaSecuritySpec (F ⊕ G) G G) Bool) :
    evalDist (do
      let b ← ($ᵗ F : ProbComp F)
      let a ← ($ᵗ F : ProbComp F)
      (simulateQ (honestImpl_lazy_real gp gen a b) adversary).run' s) =
    evalDist ((simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run' s) := by
  induction adversary using OracleComp.inductionOn generalizing s with
  | pure x =>
    -- Both sides reduce to `pure x` after `simulateQ_pure` + `StateT.run'_pure`;
    -- on LHS the external samples `b, a` become a constant bind which collapses
    -- to `pure x` since `$ᵗ F` has zero failure probability.
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    refine evalDist_ext fun y => ?_
    rw [probOutput_bind_const, probOutput_bind_const]
    simp [probFailure_uniformSample]
  | query_bind t k ih =>
    -- Decompose: `simulateQ impl (query t >>= k) = (impl t).run >>= fun (u, s') =>
    --   simulateQ impl (k u) .run' s'`. Case on `t : ckaSecuritySpec.Domain`.
    -- The 9 oracle cases split into:
    --   * 5 non-divergence (impl_lazy = impl_reg pointwise): unifSpec, recvA,
    --     recvB, corruptA, corruptB. Bind-swap + IH.
    --   * 4 conditional-divergence (party-split): sendA, sendB, challA, challB.
    --     Off-party: same as non-divergence. On-party with embedding/challenge:
    --     bijection `a ↔ x'` or `b ↔ x` via `probOutput_bind_bijective_uniform_cross`.
    match t with
    | OUnif _ =>  -- unifSpec
      exact evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ _ => rfl) ih
    | ORecvA =>  -- recvA
      exact evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ _ => rfl) ih
    | ORecvB =>  -- recvB
      exact evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ _ => rfl) ih
    | OCorruptA =>  -- corruptA
      exact evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ _ => rfl) ih
    | OCorruptB =>  -- corruptB
      exact evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
        (fun _ _ => rfl) ih
    | OSendA =>  -- sendA
      -- Case-split on `gp.challengedParty`:
      -- • P=A (off-party): impl_eq via `honestSendA_lazy_run_eq_at_P_A`, then passthrough.
      -- • P=B (on-party): embedding event; bijection coupling needed
      --   (see `On-party bijection roadmap` doc-comment above the bridge lemma).
      cases h_cp : gp.challengedParty with
      | A =>
        refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
          (fun a _ => ?_) ih
        exact honestSendA_lazy_run_eq_at_P_A (gen := gen) gp h_cp a s
      | B =>
        -- On-party embedding for sendA-P=B.
        -- Use `evalDist_marginalized_honestSendA_lazy_eq_oracleSendA_at_P_B` to convert
        -- the impl-call marginal `do a ← $F; (honestSendA_lazy gp gen a ()).run s`
        -- to `(oracleSendA cka ()).run s`. The continuation `(sim_lazy(a, b) (k p.1)).run' p.2`
        -- depends on `a` AND `b`; the post-event a-independence (when the embedding fires,
        -- the post-state has stA = .inl _ and state.tA ≥ gp.tStar, so subsequent embedding
        -- queries can't fire and lazy is a-independent at the rest of the trace) is the
        -- additional ingredient needed beyond the helper.
        -- Spike conclusion (2026-04-29): upstream `rvcgen` times out on this goal due to
        -- impl-body complexity; targeted `apply evalDist_eq_of_relTriple_eqRel` + `simp` +
        -- manual `relTriple_bind_uniformSample_bij` works but saves only ~30-45 lines/case
        -- vs the manual `probOutput_bind_*` chain. Continuing with the manual approach
        -- using existing bijection helpers + post-event a-indep + IH.
        sorry
    | OSendB =>  -- sendB
      cases h_cp : gp.challengedParty with
      | A => sorry  -- On-party embedding for sendB: bijection a ↔ (eager x).
      | B =>
        refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
          (fun a _ => ?_) ih
        exact honestSendB_lazy_run_eq_at_P_B (gen := gen) gp h_cp a s
    | OChallA =>  -- challA
      cases h_cp : gp.challengedParty with
      | A => sorry  -- On-party challenge for challA: bijection b ↔ (eager x).
      | B =>
        refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
          (fun _ b => ?_) ih
        exact honestChallA_lazy_run_eq_at_P_B (gen := gen) gp h_cp b s
    | OChallB =>  -- challB
      cases h_cp : gp.challengedParty with
      | A =>
        refine evalDist_eager_honest_lazy_eq_step_passthrough (gen := gen) gp s _ k
          (fun _ b => ?_) ih
        exact honestChallB_lazy_run_eq_at_P_A (gen := gen) gp h_cp b s
      | B => sorry  -- On-party challenge for challB: bijection b ↔ (eager x).

private lemma probOutput_lazy_honest_eq (gp : GameParams)
    (adversary : CKAAdversary (F ⊕ G) G G) (x₀ : F) :
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl_lazy_real gp gen) adversary).run
        ((initGameState (.inr (x₀ • gen)) (.inl x₀) false, none), none)
      return b'] =
    Pr[= false | do
      let (b', _) ← (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      return b'] := by
  -- Compose Step 1 (consumeLazy commutation × 2) and Step 2 (adversary
  -- induction via bijection at hits + bind-swap at non-hits).
  have h₁ := evalDist_ckaSecurityImpl_lazy_eq_eager (gen := gen) gp adversary
    (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  have h₂ := evalDist_eager_honest_lazy_eq (gen := gen) gp
    (initGameState (.inr (x₀ • gen)) (.inl x₀) false) adversary
  show evalDist _ false = evalDist _ false
  exact congr_fun (congr_arg DFunLike.coe (h₁.trans h₂)) false

omit [Fintype G] in
/-- General-case per-fixed-`x₀` claim: with `a, b ← $ᵗ F` and honest init
`(.inr (x₀•gen), .inl x₀)`, the reduction's output distribution equals
honest's. This is the "heart" of Step (2)'s general case — the
`consumeLazy`-peel + state-relation bridge lives here. -/
private lemma probOutput_general_per_x₀ (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
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

omit [Fintype G] in
/-- General-case (`¬ (t* = 1 ∧ P = A)`) game-level bridge.

Stated with `x₀ ← $ᵗ F` sampled *inside* on both sides (matching the shape
Step (2)'s dispatch produces after `simp only [reductionInitState, if_neg]`).

Proof: swap `x₀` to outermost on LHS (3-way bind manipulation), then apply
`probOutput_bind_congr'` on the shared outer `x₀` and close each fiber via
`probOutput_general_per_x₀`. -/
private lemma probOutput_general_pointwise (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
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
        exact probOutput_general_per_x₀ gp hΔ h_not_special adversary x₀

omit [Fintype G] in
/-- Special-case per-fixed-`x₀` claim: with the rename `a ↔ x₀`, reduction's
init `(.inr (x₀•gen), .inl 0)` (stB dead) and honest's `(.inr (x₀•gen), .inl x₀)`
produce the same output distribution after the remaining `b ← $ᵗ F` peel. -/
private lemma probOutput_special_per_x₀ (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_special : gp.tStar = 1 ∧ gp.challengedParty = .A)
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

omit [Fintype G] in
/-- Special-case (`gp = ⟨1, _, .A⟩`) bridge: reduction init `(.inr (a•gen), .inl 0)`
with outer `a ←$ F` equals honest init `(.inr (x₀•gen), .inl x₀)` with
outer `x₀ ←$ F` (renaming `a ↔ x₀`), averaged over the remaining `b ←$ F`. -/
private lemma probOutput_special_pointwise (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (h_special : gp.tStar = 1 ∧ gp.challengedParty = .A)
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
  exact probOutput_special_per_x₀ gp hΔ h_special adversary x₀

omit [Fintype G] in
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
  by_cases h_special : gp.tStar = 1 ∧ gp.challengedParty = .A
  · -- Special: `reductionInitState` = `pure (init .inr gA .inl 0)` (no x₀ sample).
    simp only [reductionInitState, if_pos h_special, pure_bind]
    exact probOutput_special_pointwise (gen := gen) gp hΔ h_special adversary
  · -- General: `reductionInitState` = `do x₀ ← $F; pure (init .inr (x₀•gen) .inl x₀)`.
    simp only [reductionInitState, if_neg h_special, bind_assoc, pure_bind]
    exact probOutput_general_pointwise (gen := gen) gp hΔ h_special adversary

omit [Fintype G] in
/-- General-case rand-branch per-fixed-`x₀` claim. With `a, b, c ← $ᵗ F`,
reduction's output on `init .inr (x₀•gen) .inl x₀ false` matches honest's on
the same state with `b = true`. Couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
private lemma probOutput_general_per_x₀_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
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

omit [Fintype G] in
/-- General-case (`¬ (t* = 1 ∧ P = A)`) rand-branch game-level bridge.
Analogue of `probOutput_general_pointwise` with the extra `c ← $ᵗ F`
sampled internally; challenge couples `c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
private lemma probOutput_general_pointwise_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_not_special : ¬ (gp.tStar = 1 ∧ gp.challengedParty = .A))
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
        refine probOutput_bind_congr' _ false fun a => ?_2
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
        exact probOutput_general_per_x₀_rand gp hΔ hg h_not_special adversary x₀

omit [Fintype G] in
/-- Special-case rand-branch per-fixed-`x₀` claim: after renaming `a ↔ x₀`,
reduction's init `(.inr (x₀•gen), .inl 0)` with remaining `b, c ← $ᵗ F`
matches honest's init `(.inr (x₀•gen), .inl x₀)` with `b = true`. Couples
`c•gen ↔ outKey ← $ᵗ G` via `hg`. -/
private lemma probOutput_special_per_x₀_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_special : gp.tStar = 1 ∧ gp.challengedParty = .A)
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

omit [Fintype G] in
/-- Special-case (`gp = ⟨1, _, .A⟩`) rand-branch bridge. Analogue of
`probOutput_special_pointwise`; reduction's init is `(.inr (a•gen), .inl 0)`
with `c` replacing `a*b` in `gT`; rename `a ↔ x₀`, couple
`c•gen ↔ outKey ← $ᵗ G` via `hg` at the challenge. -/
private lemma probOutput_special_pointwise_rand (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (h_special : gp.tStar = 1 ∧ gp.challengedParty = .A)
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
  exact probOutput_special_per_x₀_rand gp hΔ hg h_special adversary x₀

omit [Fintype G] in
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
  by_cases h_special : gp.tStar = 1 ∧ gp.challengedParty = .A
  · simp only [reductionInitState, if_pos h_special, pure_bind]
    exact probOutput_special_pointwise_rand (gen := gen) gp hΔ hg h_special adversary
  · simp only [reductionInitState, if_neg h_special, bind_assoc, pure_bind]
    exact probOutput_general_pointwise_rand (gen := gen) gp hΔ hg h_special adversary

omit [Fintype G] in
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

omit [Fintype G] in
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

omit [Fintype G] in
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

omit [Inhabited F] [Fintype G] in
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

omit [Fintype G] in
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

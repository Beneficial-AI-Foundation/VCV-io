import Examples.CKA.FromDDH.Common
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.ProgramLogic.Tactics.Common.OracleSum

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
`securityAdvantage(ddhCKA, 𝒜, ⟨tStar, 1, P⟩) ≤ ddhGuessAdvantage(gen, ℬ)`,
with no multiplicative loss.*

### `ΔCKA = 1`

`ΔCKA = 1` in the main theorem means the adversary is allowed to corrupt
party `Q` only if `tQ ≥ tStar + ΔCKA`: one more action after the challenge.
This is the smallest `ΔCKA` that works — with `ΔCKA = 0`:
- Corrupting the challenged party `P` immediately after the challenge would
  reveal the fresh scalar `z` used by the reduction.
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

The given CKA adversary `𝒜` challenges exactly one party at epoch `t*`.
We show the case where `𝒜` calls `O-Chall-A` at `tA = t*`.

Given a DDH triple `(gen, gA, gB, gT)` with
`gA = a • gen`,`gB = b • gen`, and `gT = c • gen` where `c = a·b` (real) or `c` is uniform:

```text
 DDH Challenger                 DDH Adversary ℬ = securityReduction gp 𝒜
┌──────────────┐               ┌──────────────────────────────────────────────────────────┐
│              │ (gen,gA,gB,gT)│ sample x₀ ←$ F                                           │
│  gA = a•gen  │──────────────▶│ init A with g₀ := x₀ • gen, init B with x₀               │
│  gB = b•gen  │               │                                                          │
│  gT = c•gen  │               │ simulate CKA oracles for 𝒜 (honest except below):        │
│              │               │                                                          │
│  c = a·b     │               │          Honest CKA    │ Hybrid        │ Reduction       │
│  or random   │               │ ─────────────────────────────────────────────────────────│
│              │               │ O-Send-B, tB = t* - 1, stA = xA ∈ F, stB = xA•gen ∈ G    │
│              │               │   y ←$ F               │               │                 │
│              │               │   ρ   = y • gen        │ ρ   = gA      │ ρ   = gA        │
│              │               │   key = y • xA • gen   │ key = xA • gA │ key = xA • gA   │
│              │               │   stB := y             │ stB := a      │ stB := y        │
│              │               │ ─────────────────────────────────────────────────────────│
│              │               │ recvA delivers ρ from above:                             │
│              │               │   stA := y • gen       │ stA := gA     │ stA := gA       │
│              │               │ ─────────────────────────────────────────────────────────│
│              │               │ O-Chall-A, tA = t*, (stA, stB) as updated above:         │
│              │               │   x ←$ F               │               │                 │
│              │               │   ρ   = x • gen        │ ρ   = gB      │ ρ   = gB        │
│              │               │   key = x • stA        │ key = gT      │ key = gT        │
│              │               │   stA := x             │ stA := b      │ stA := z        │
│              │               │ · · · · · · · · · · · · · · · · · · · · · · · · · · · · ·│
│              │               │   real: gT = b • gA                random: gT ←$ G       │
│              │               │ ─────────────────────────────────────────────────────────│
│              │               │ all later queries: honest in all three                   │
│              │               │                                                          │
│              │     !b'       │ output !b', where b' is 𝒜's challenge guess              │
│              │◀──────────────│                                                          │
└──────────────┘               └──────────────────────────────────────────────────────────┘
```

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

The reduction receives a DDH tuple `(G, aG, bG, gT)` where `a, b ← $F` and
either `gT = abG` (real) or `gT = cG` for `c ← $F` (random). -/

/-- **O-Send-B** (modified for DDH reduction). `() → Option (ρ : G, key : G)`.

At `tB = t* - 1` (embedding epoch), with state `(stA, stB) = (xA ∈ F, h ∈ G)`:
- Reduction: `(ρ, key) = (aG, xA · aG)` — embeds DDH element `aG`
- Honest CKA: `(ρ, key) = (y · G, y · xA · G)` for `y ← $F`
- Same distribution since `a` is uniform like `y`
- Update: `(stA, stB, tB) ← (xA, y ∈ F, tB + 1)` for fresh `y ← $F`

All other epochs: delegates to `oracleSendB`. -/
private noncomputable def reductionSendB (gp : GameParams) (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      let state := { state with tB := state.tB + 1 }
      if gp.challengedParty == .A && isOtherSendBeforeChall gp state then
        -- embedding epoch: xA = stA ∈ F
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        -- y ← $F (independent of a; hidden state diverges from hybrid)
        let y ← liftM ($ᵗ F : ProbComp F)
        -- ρ := aG, key := xA · aG, stB := y
        set { state with
          stB := (.inl y : F ⊕ G), lastRhoB := some gA, lastKeyB := some (xA • gA),
          lastAction := some .sendB }
        return some (gA, xA • gA)
      else
        match ← liftM (ddhCKA.send gen state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          set { state with
            stB := stB', lastRhoB := some ρ, lastKeyB := some key,
            lastAction := some .sendB }
          return some (ρ, key)
    else pure none

/-- **O-Send-A** (modified for DDH reduction, symmetric to `reductionSendB`).
`() → Option (ρ : G, key : G)`.

At `tA = t*` (embedding epoch), with state `(stA, stB) = (h ∈ G, xB ∈ F)`:
- Reduction: `(ρ, key) = (aG, xB · aG)` — embeds DDH element `aG`
- Honest CKA: `(ρ, key) = (x · G, x · xB · G)` for `x ← $F`
- Same distribution since `a` is uniform like `x`
- Update: `(stA, stB, tA) ← (y ∈ F, xB, tA + 1)` for fresh `y ← $F`

All other epochs: delegates to `oracleSendA`. -/
private noncomputable def reductionSendA (gp : GameParams) (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      let state := { state with tA := state.tA + 1 }
      if gp.challengedParty == .B && isOtherSendBeforeChall gp state then
        -- embedding epoch: xB = stB ∈ F
        let xB := match state.stB with | .inl x => x | .inr _ => 0
        -- y ← $F (independent of a; hidden state diverges from hybrid)
        let y ← liftM ($ᵗ F : ProbComp F)
        -- ρ := aG, key := xB · aG, stA := y
        set { state with
          stA := (.inl y : F ⊕ G), lastRhoA := some gA, lastKeyA := some (xB • gA),
          lastAction := some .sendA }
        return some (gA, xB • gA)
      else
        match ← liftM (ddhCKA.send gen state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          set { state with
            stA := stA', lastRhoA := some ρ, lastKeyA := some key,
            lastAction := some .sendA }
          return some (ρ, key)
    else pure none

/-- **O-Chall-A** (modified for DDH reduction). `() → Option (ρ : G, key : G)`.

At `tA = t*`:
With state `(stA, stB) = (aG ∈ G, xB ∈ F)`:
- Reduction: `(ρ, key) = (gB, gT)` directly from DDH tuple
- Honest CKA: `(ρ, key) = (x · G, x · aG)` for `x ← $F`
- Real DDH: `(gB, gT) = (bG, b · aG)` by `smul_comm`; same distribution
- Random DDH: `gT = cG` for uniform `c`, matching `$ᵗ G`
- Update: `(stA, tA) ← (z ∈ F, tA + 1)` for fresh `z ← $F` (not `b`);
  `ΔCKA = 1` prevents corruption before `z` is overwritten -/
private noncomputable def reductionChallA (gp : GameParams) (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .A && validStep state.lastAction .challA then
      let state := { state with tA := state.tA + 1 }
      if isChallengeEpoch gp state then
        let z ← liftM ($ᵗ F : ProbComp F)
        -- z ← $F independent of b; ρ := gB, key := gT, stA := z
        set { state with
          stA := (.inl z : F ⊕ G),
          lastRhoA := some gB, lastKeyA := some gT,
          lastAction := some .challA }
        return some (gB, gT)
      else pure none
    else pure none

/-- **O-Chall-B** (modified for DDH reduction, symmetric to `reductionChallA`).
`() → Option (ρ : G, key : G)`.

With state `(stA, stB) = (xA ∈ F, bG ∈ G)`:
- Output: `(ρ, key) = (gB, gT)` from DDH tuple
- Update: `(stB, tB) ← (z ∈ F, tB + 1)` for fresh `z ← $F` -/
private noncomputable def reductionChallB (gp : GameParams) (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .B && validStep state.lastAction .challB then
      let state := { state with tB := state.tB + 1 }
      if isChallengeEpoch gp state then
        let z ← liftM ($ᵗ F : ProbComp F)
        -- z ← $F independent of b; ρ := gB, key := gT, stB := z
        set { state with
          stB := (.inl z : F ⊕ G),
          lastRhoB := some gB, lastKeyB := some gT,
          lastAction := some .challB }
        return some (gB, gT)
      else pure none
    else pure none

/-- Oracle implementation `R(g, aG, bG, gT)` for the DDH reduction.

Embeds the DDH tuple into the oracles for `challengedParty` (read from state):
- The other party's send embeds `aG` at `isOtherSendBeforeChall`
- The challenge oracle embeds `(gB, gT)` at `isChallengeEpoch`

All modified oracles are always present; each guards on `challengedParty`
internally, so only the relevant ones fire. -/
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

Given a DDH triple `(gen, gA, gB, gT)`, the reduction:
1. Initialises the CKA game honestly: `x₀ ← $ᵗ F`.
2. Runs the adversary against `reductionOracleImpl`, which embeds `aG` into
   the other party's send and `(gB, gT)` into `gp.challengedParty`'s challenge.
3. Outputs `!b'` (negated CKA guess) to align bit conventions. -/
noncomputable def securityReduction (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : DDHAdversary F G :=
  fun gen gA gB gT => do
    let x₀ ← $ᵗ F
    let (b', _) ← (simulateQ (reductionOracleImpl gp gen gA gB gT) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
    return !b'

/-! ### Simulation: each DDH branch maps to the corresponding CKA branch

The goal is to show that the adversary `𝒜` has the same view whether it interacts with the
real CKA game or with the reduction's simulation.

The reduction `ℬ` returns `¬b'`. We show (see the module overview above):

    Pr[ℬ ⇒ 1 | DDH_real] = Pr[𝒜 ⇒ 0 | CKA^{b=0}]   … (real)
    Pr[ℬ ⇒ 1 | DDH_rand] = Pr[𝒜 ⇒ 0 | CKA^{b=1}]   … (rand)

The **real branch** uses three games (columns in the diagram above):

- `G_R`   — `securityReductionRealGame`:  `𝒜` vs `reductionOracleImpl` (Reduction)
- `G_H`   — `securityHybridGame`:       `𝒜` vs `hybridOracleImpl`          (Hybrid)
- `G_CKA` — `securityExpFixedBitFalseGame`: `𝒜` vs `ckaSecurityImpl` (Honest CKA)

    Pr[ℬ ⇒ 1 | DDH_real]
      = Pr[G_R   ⇒ 0]        (ℬ negates; `probOutput_not_map`)
      = Pr[G_H   ⇒ 0]        (`securityReduction_real_to_hybrid`)
      = Pr[G_CKA ⇒ 0]        (`securityReduction_hybrid_to_honest`)  ∎

The **random branch** follows from bijectivity of `(·) • gen`: `c • gen ≡ $ᵗ G`.
-/

/-- Auxiliary game `G_real(𝒜)`: samples `a, b, x₀ ← $F`, runs `𝒜` against
`R = reductionOracleImpl(g, ag, bg, abg)`, and returns `b'` (without negation).

The full reduction returns `¬b'`, so `Pr[ℬ = true | real DDH] = Pr[G_real = false]`
by `probOutput_not_map`. The bridge lemmas then show
`Pr[G_real = false] = Pr[CKA(b=false) = false]`, completing `securityReduction_real`. -/
private noncomputable def securityReductionRealGame (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- Unfold the real DDH branch of the reduction into the explicit helper game
`securityReductionRealGame`. -/
private lemma probOutput_ddhExpReal_securityReduction (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpReal securityReduction
  simpa [securityReductionRealGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRealGame (gen := gen) gp adversary))

/-- The fixed-bit CKA security game with `b = false`, written explicitly with the
initial key sample exposed. -/
private noncomputable def securityExpFixedBitFalseGame (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- Unfold the fixed-bit `b = false` branch into the explicit helper game
`securityExpFixedBitFalseGame`. -/
private lemma probOutput_securityExpFixedBit_false (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpFixedBitFalseGame ddhCKA
  simp [initGameState]

/-! ### Hybrid oracles

The reduction's send oracles (`reductionSendA`/`reductionSendB`) embed `aG` at
the special epoch but sample a fresh independent scalar for the party's hidden
state.  The hybrid variants below instead set the hidden state to `a` itself
(i.e. `stA := a` or `stB := a`), matching the honest game when `a` is uniform.

Concretely, at the embedding epoch:

| Oracle         | Output   | Hidden state |
|----------------|----------|--------------|
| honest         | `y • G`  | `y`          |
| **hybrid**     | `a • G`  | `a`          |
| reduction      | `a • G`  | `y ← $F`    |

When `a ← $F`, the hybrid is identical in distribution to the honest game.
The bridge lemmas below show that the reduction's game rewrites into the
hybrid, then into `securityExpFixedBit` with `b = false`.
-/

/-- Hybrid A-send (real branch): at the epoch before `challB`, outputs `a • gen`
and sets `stA := a`, reusing the external DDH scalar instead of sampling fresh. -/
private noncomputable def hybridSendA (gp : GameParams) (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      let state := { state with tA := state.tA + 1 }
      if gp.challengedParty == .B && isOtherSendBeforeChall gp state then
        -- embedding epoch: ρ := a·G, key := xB · a·G, stA := a
        let gA := a • gen
        let xB := match state.stB with | .inl x => x | .inr _ => 0
        set { state with
          stA := (.inl a : F ⊕ G), lastRhoA := some gA, lastKeyA := some (xB • gA),
          lastAction := some .sendA }
        return some (gA, xB • gA)
      else
        match ← liftM (ddhCKA.send gen state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          set { state with
            stA := stA', lastRhoA := some ρ, lastKeyA := some key,
            lastAction := some .sendA }
          return some (ρ, key)
    else pure none

/-- Hybrid B-send (real branch): at the epoch before `challA`, outputs `a • gen`
and sets `stB := a`, reusing the external DDH scalar instead of sampling fresh. -/
private noncomputable def hybridSendB (gp : GameParams) (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      let state := { state with tB := state.tB + 1 }
      if gp.challengedParty == .A && isOtherSendBeforeChall gp state then
        -- embedding epoch: ρ := a·G, key := xA · a·G, stB := a
        let gA := a • gen
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        set { state with
          stB := (.inl a : F ⊕ G), lastRhoB := some gA, lastKeyB := some (xA • gA),
          lastAction := some .sendB }
        return some (gA, xA • gA)
      else
        match ← liftM (ddhCKA.send gen state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          set { state with
            stB := stB', lastRhoB := some ρ, lastKeyB := some key,
            lastAction := some .sendB }
          return some (ρ, key)
    else pure none

/-- Hybrid A-challenge: at the challenge epoch, `ρ := b·G`, `key := ab·G`,
`stA := b`. Matches the honest game when `b ← $F`. -/
private noncomputable def hybridChallA (gp : GameParams) (gen : G) (a b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .A && validStep state.lastAction .challA then
      let state := { state with tA := state.tA + 1 }
      if isChallengeEpoch gp state then
        -- ρ := bG, key := abG, stA := b
        let gB := b • gen
        let gT := (a * b) • gen
        set { state with
          stA := (.inl b : F ⊕ G),
          lastRhoA := some gB, lastKeyA := some gT,
          lastAction := some .challA }
        return some (gB, gT)
      else pure none
    else pure none

/-- Hybrid B-challenge: at the challenge epoch, `ρ := b·G`, `key := ab·G`,
`stB := b`. Matches the honest game when `b ← $F`. -/
private noncomputable def hybridChallB (gp : GameParams) (gen : G) (a b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if gp.challengedParty == .B && validStep state.lastAction .challB then
      let state := { state with tB := state.tB + 1 }
      if isChallengeEpoch gp state then
        -- ρ := bG, key := abG, stB := b
        let gB := b • gen
        let gT := (a * b) • gen
        set { state with
          stB := (.inl b : F ⊕ G),
          lastRhoB := some gB, lastKeyB := some gT,
          lastAction := some .challB }
        return some (gB, gT)
      else pure none
    else pure none

/-- Hybrid oracle implementation: same visible DDH embedding as
`reductionOracleImpl`, but the hidden states at the special send/challenge
epochs use the DDH scalars `a, b` instead of fresh randomness. -/
private noncomputable def hybridOracleImpl (gp : GameParams) (gen : G) (a b : F) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  (oracleUnif (F ⊕ G) G G
    + hybridSendA (F := F) gp gen a
    + oracleRecvA (ddhCKA F G gen)
    + hybridSendB (F := F) gp gen a
    + oracleRecvB (ddhCKA F G gen))
  + hybridChallA (F := F) gp gen a b
  + hybridChallB (F := F) gp gen a b
  + oracleCorruptA gp (F ⊕ G) G G
  + oracleCorruptB gp (F ⊕ G) G G

/-- The explicit game induced by `hybridOracleImpl`. -/
private noncomputable def securityHybridGame (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (hybridOracleImpl (F := F) gp gen a b) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- State map `π : GameState → GameState` from `R`-states to `H`-states,
where `R := reductionOracleImpl(g, aG, bG, abG)` and `H := hybridOracleImpl(g, a, b)`.

`R` and `H` agree on all outputs but diverge on hidden party state at the two
embedding epochs for the challenged direction:

- if `challengedParty = .A`, then `π` rewrites B's special send-state to `a`
  and A's special challenge-state to `b`
- if `challengedParty = .B`, then `π` rewrites A's special send-state to `a`
  and B's special challenge-state to `b`
- it also forgets the internal `correct` flag, which is unobservable in the
  security game and can differ spuriously in the reduction after the embedded
  challenge branch

All other fields (outputs, counters, flags) pass through unchanged. -/
private noncomputable def hybridProj (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) : GameState (F ⊕ G) G G :=
  { s with
    correct := true
    stA := match gp.challengedParty, s.stA with
      | .A, .inl _ =>
          if (s.lastAction = some .challA && s.tA == gp.tStar) ||
              (s.lastAction = some .recvB && s.tA == gp.tStar &&
                s.stB = (.inr (b • gen) : F ⊕ G)) ||
              (s.lastAction = some .sendB && s.tA == gp.tStar &&
                s.tB == gp.tStar + 1)
          then (.inl b : F ⊕ G)
          else s.stA
      | .B, .inl _ =>
          if s.tA == gp.tStar &&
              (s.lastAction = some .sendA ||
               (s.lastAction = some .recvB &&
                 s.stB = (.inr (a • gen) : F ⊕ G)) ||
               s.lastAction = some .sendB ||
               s.lastAction = some .challB)
          then (.inl a : F ⊕ G)
          else s.stA
      | _, .inr _ => s.stA
    stB := match gp.challengedParty, s.stB with
      | .A, .inl _ =>
          if s.tB == gp.tStar - 1 &&
              (s.lastAction = some .sendB ||
               s.lastAction = some .recvA ||
               s.lastAction = some .sendA ||
               s.lastAction = some .challA)
          then (.inl a : F ⊕ G)
          else s.stB
      | .B, .inl _ =>
          if s.tB == gp.tStar &&
              (s.lastAction = some .challB ||
               s.lastAction = some .recvA ||
               s.lastAction = some .sendA)
          then (.inl b : F ⊕ G)
          else s.stB
      | _, .inr _ => s.stB }

/-- Reduction-side witness for the short post-challenge window where the reduction and
the hybrid differ only in hidden state.

At the challenged challenge step, this records the DDH transcript still pending on the
wire. At the following receive step, it records that the receiver now stores the DDH
challenge message. Outside these windows, the predicate is trivial. This is exactly the
extra fact needed to justify the rewrites performed by `hybridProj`. -/
private def hybridWindowInv (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) : Prop :=
  match gp.challengedParty, s.lastAction with
  | .A, some .challA =>
      s.tA = gp.tStar →
        s.lastRhoA = some (b • gen) ∧
        s.lastKeyA = some ((a * b) • gen)
  | .A, some .recvB =>
      s.tA = gp.tStar →
        s.stB = (.inr (b • gen) : F ⊕ G)
  | .B, some .challB =>
      s.tB = gp.tStar →
        s.lastRhoB = some (b • gen) ∧
        s.lastKeyB = some ((a * b) • gen)
  | .B, some .recvA =>
      s.tB = gp.tStar →
        s.stA = (.inr (b • gen) : F ⊕ G)
  | _, _ => True

/-
Notation for the bridge below:
- `sR` is the concrete reduction state.
- `sH` is the corresponding hybrid state, obtained from `sR` by `hybridProj`.
- `hybridWindowInv` marks the brief post-challenge interval where the two games may
  disagree internally, while still exposing the same oracle outputs.
-/
/-- Relational invariant between reduction and hybrid states.

`sH = hybridProj sR` gives the projection; `reachableShape sR` captures the shape
invariant on the reduction side (correct-flag is normalized away by `hybridProj`);
`hybridWindowInv sR` records the extra facts about the challenged branch needed
to justify the projection. -/
private def hybridRel (gp : GameParams) (a b : F)
    (sR sH : GameState (F ⊕ G) G G) : Prop :=
  sH = hybridProj (F := F) (gen := gen) gp a b sR ∧
  reachableShape gen sR ∧
  hybridWindowInv (F := F) (G := G) (gen := gen) gp a b sR

/-- Map a reduction-side post-state to the corresponding hybrid-side post-state. -/
private noncomputable def hybridPostMap {α : Type} (gp : GameParams) (a b : F)
    (p : α × GameState (F ⊕ G) G G) : α × GameState (F ⊕ G) G G :=
  (p.1, hybridProj (F := F) (gen := gen) gp a b p.2)

section hybridHelpers
omit [Fintype F] [SampleableType F] [SampleableType G]

/-- If the reduction-side shape holds and the window witness holds, then the pair
`(s, hybridProj s)` satisfies `hybridRel`. -/
private lemma hybridRel_mk (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G)
    (hShape : reachableShape gen s)
    (hWin : hybridWindowInv (F := F) (G := G) (gen := gen) gp a b s) :
    hybridRel (F := F) (G := G) (gen := gen) gp a b s
      (hybridProj (F := F) (gen := gen) gp a b s) :=
  ⟨rfl, hShape, hWin⟩

section windowAndReachable
omit [DecidableEq F] [DecidableEq G]

/-- In the challenged-`A` challenge window, `hybridWindowInv` identifies the pending
challenge transcript as `(b • gen, (a * b) • gen)`. -/
private lemma hybridWindowInv_A_challA
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .A)
    (hact : s.lastAction = some .challA)
    (hWin : hybridWindowInv (F := F) (G := G) (gen := gen) gp a b s)
    (htA : s.tA = gp.tStar) :
    s.lastRhoA = some (b • gen) ∧
      s.lastKeyA = some ((a * b) • gen) := by
  have hWin' : s.tA = gp.tStar →
      s.lastRhoA = some (b • gen) ∧
        s.lastKeyA = some ((a * b) • gen) := by
    simpa [hybridWindowInv, hcp, hact] using hWin
  exact hWin' htA

/-- In the challenged-`A` post-`recvB` window, `hybridWindowInv` identifies B's
received state as the DDH challenge message `b • gen`. -/
private lemma hybridWindowInv_A_recvB
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .A)
    (hact : s.lastAction = some .recvB)
    (hWin : hybridWindowInv (F := F) (G := G) (gen := gen) gp a b s)
    (htA : s.tA = gp.tStar) :
    s.stB = (.inr (b • gen) : F ⊕ G) := by
  have hWin' : s.tA = gp.tStar →
      s.stB = (.inr (b • gen) : F ⊕ G) := by
    simpa [hybridWindowInv, hcp, hact] using hWin
  exact hWin' htA

/-- Symmetric extraction of the pending challenge transcript in the challenged-`B`
challenge window. -/
private lemma hybridWindowInv_B_challB
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .B)
    (hact : s.lastAction = some .challB)
    (hWin : hybridWindowInv (F := F) (G := G) (gen := gen) gp a b s)
    (htB : s.tB = gp.tStar) :
    s.lastRhoB = some (b • gen) ∧
      s.lastKeyB = some ((a * b) • gen) := by
  have hWin' : s.tB = gp.tStar →
      s.lastRhoB = some (b • gen) ∧
        s.lastKeyB = some ((a * b) • gen) := by
    simpa [hybridWindowInv, hcp, hact] using hWin
  exact hWin' htB

/-- Symmetric extraction of the delivered DDH challenge message after `recvA` when B
is challenged. -/
private lemma hybridWindowInv_B_recvA
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .B)
    (hact : s.lastAction = some .recvA)
    (hWin : hybridWindowInv (F := F) (G := G) (gen := gen) gp a b s)
    (htB : s.tB = gp.tStar) :
    s.stA = (.inr (b • gen) : F ⊕ G) := by
  have hWin' : s.tB = gp.tStar →
      s.stA = (.inr (b • gen) : F ⊕ G) := by
    simpa [hybridWindowInv, hcp, hact] using hWin
  exact hWin' htB

/-- The reduction's challenged-`A` challenge post-state automatically satisfies the
challenge-window witness. -/
private lemma hybridWindowInv_reductionChallA_post
    (gp : GameParams) (a b z : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .A) :
    hybridWindowInv (F := F) (G := G) (gen := gen) gp a b
      { s with
        tA := s.tA + 1
        stA := (.inl z : F ⊕ G)
        lastRhoA := some (b • gen)
        lastKeyA := some ((a * b) • gen)
        lastAction := some .challA } := by
  unfold hybridWindowInv
  simp [hcp]

/-- After `recvB` in the challenged-`A` window, storing `b • gen` on B's side is
exactly the witness demanded by `hybridWindowInv`. -/
private lemma hybridWindowInv_oracleRecvB_post
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .A) :
    hybridWindowInv (F := F) (G := G) (gen := gen) gp a b
      { s with
        stB := (.inr (b • gen) : F ⊕ G)
        lastRhoA := none
        lastKeyA := none
        lastAction := some .recvB } := by
  unfold hybridWindowInv
  simp [hcp]

/-- Symmetric post-state witness for the reduction's challenged-`B` challenge step. -/
private lemma hybridWindowInv_reductionChallB_post
    (gp : GameParams) (a b z : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .B) :
    hybridWindowInv (F := F) (G := G) (gen := gen) gp a b
      { s with
        tB := s.tB + 1
        stB := (.inl z : F ⊕ G)
        lastRhoB := some (b • gen)
        lastKeyB := some ((a * b) • gen)
        lastAction := some .challB } := by
  unfold hybridWindowInv
  simp [hcp]

/-- Symmetric post-state witness after `recvA` when B is challenged. -/
private lemma hybridWindowInv_oracleRecvA_post
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hcp : gp.challengedParty = .B) :
    hybridWindowInv (F := F) (G := G) (gen := gen) gp a b
      { s with
        stA := (.inr (b • gen) : F ⊕ G)
        lastRhoB := none
        lastKeyB := none
        lastAction := some .recvA } := by
  unfold hybridWindowInv
  simp [hcp]

/-- A reachable state with `lastAction = none` or `recvA` is in the synchronous
`(x • gen, x)` phase. -/
private lemma reachableInv_none_or_recvA
    (s : GameState (F ⊕ G) G G)
    (hInv : reachableInv gen s)
    (hact : s.lastAction = none ∨ s.lastAction = some .recvA) :
    ∃ x : F, s.stA = .inr (x • gen) ∧ s.stB = .inl x ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none := by
  rcases hInv with ⟨_, _, hshape⟩
  cases hact with
  | inl hnone =>
      simpa [phaseShapeInv, hnone] using hshape
  | inr hrecvA =>
      simpa [phaseShapeInv, hrecvA] using hshape

/-- A reachable state with `lastAction = sendA` or `challA` is in the pending
`A → B` phase with scalar witnesses on both sides. -/
private lemma reachableInv_sendA_or_challA
    (s : GameState (F ⊕ G) G G)
    (hInv : reachableInv gen s)
    (hact : s.lastAction = some .sendA ∨ s.lastAction = some .challA) :
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.lastRhoA = some (y • gen) ∧ s.lastRhoB = none ∧
      s.lastKeyA = some (y • (x • gen)) ∧ s.lastKeyB = none := by
  rcases hInv with ⟨_, _, hshape⟩
  cases hact with
  | inl hsendA =>
      simpa [phaseShapeInv, hsendA] using hshape
  | inr hchallA =>
      simpa [phaseShapeInv, hchallA] using hshape

/-- A reachable `recvB` state is the synchronous phase where B stores the received
group element `y • gen` and A stores the matching scalar `y`. -/
private lemma reachableInv_recvB
    (s : GameState (F ⊕ G) G G)
    (hInv : reachableInv gen s)
    (hact : s.lastAction = some .recvB) :
    ∃ y : F, s.stA = .inl y ∧ s.stB = .inr (y • gen) ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none := by
  rcases hInv with ⟨_, _, hshape⟩
  simpa [phaseShapeInv, hact] using hshape

/-- A reachable state with `lastAction = sendB` or `challB` is in the pending
`B → A` phase with scalar witnesses on both sides. -/
private lemma reachableInv_sendB_or_challB
    (s : GameState (F ⊕ G) G G)
    (hInv : reachableInv gen s)
    (hact : s.lastAction = some .sendB ∨ s.lastAction = some .challB) :
    ∃ x y : F, s.stA = .inl y ∧ s.stB = .inl x ∧
      s.lastRhoA = none ∧ s.lastRhoB = some (x • gen) ∧
      s.lastKeyA = none ∧ s.lastKeyB = some (x • (y • gen)) := by
  rcases hInv with ⟨_, _, hshape⟩
  cases hact with
  | inl hsendB =>
      simpa [phaseShapeInv, hsendB] using hshape
  | inr hchallB =>
      simpa [phaseShapeInv, hchallB] using hshape

end windowAndReachable

/-- The projected initial state is already an honest hybrid state. -/
private lemma hybridRel_init (gp : GameParams) (a b x₀ : F) :
    hybridRel (F := F) (G := G) (gen := gen) gp a b
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false) := by
  unfold hybridRel
  refine ⟨?_, ?_, ?_⟩
  · symm
    cases hcp : gp.challengedParty <;>
      simp [hybridProj, initGameState, hcp]
  · exact ⟨rfl, x₀, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [hybridWindowInv, initGameState]

/-- Uniform sampling preserves `hybridRel`: both sides sample the same random value
while leaving their respective states unchanged. -/
private lemma hybridRel_query_unif (gp : GameParams) (a b : F) (t : unifSpec.Domain)
    (sR sH : GameState (F ⊕ G) G G)
    (hrel : hybridRel (F := F) (G := G) (gen := gen) gp a b sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleUnif (F ⊕ G) G G t).run sR)
      ((oracleUnif (F ⊕ G) G G t).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  simpa [oracleUnif] using
    (OracleComp.ProgramLogic.Relational.relTriple_map
      (R := fun pR pH =>
        pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      (f := fun u => (u, sR)) (g := fun u => (u, sH))
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_query (spec₁ := unifSpec) t)
        (fun _ _ hEq => by
          dsimp [OracleComp.ProgramLogic.Relational.EqRel] at hEq
          subst hEq
          exact ⟨rfl, hrel⟩)))

/-- Transport a stateful computation relation from an exact left-map equality.

If mapping each left result with `f` yields exactly the right computation, then we
can couple each left sample `x` with the right sample `f x`. -/
private lemma relTriple_of_map_eq
    {α β : Type} {R : α → β → Prop}
    {oa : ProbComp α} {ob : ProbComp β}
    (f : α → β)
    (hmap : f <$> oa = ob)
    (hpost : ∀ x, x ∈ support (evalDist oa) → R x (f x)) :
    OracleComp.ProgramLogic.Relational.RelTriple oa ob R := by
  apply (OracleComp.ProgramLogic.Relational.relTriple_iff_relWP
    (oa := oa) (ob := ob) (R := R)).2
  refine ⟨⟨evalDist oa >>= fun x => pure (x, f x), ?_⟩, ?_⟩
  · constructor
    · simp
    · calc
        Prod.snd <$> (evalDist oa >>= fun x => pure (x, f x))
          = f <$> evalDist oa := by simp
        _ = evalDist (f <$> oa) := by simp [evalDist_map]
        _ = evalDist ob := by simpa using congrArg evalDist hmap
  · intro z hz
    rcases (mem_support_bind_iff
      (evalDist oa) (fun x => (pure (x, f x) : SPMF (α × β))) z).1 hz with
      ⟨x, hx, hz'⟩
    have hzEq : z = (x, f x) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    subst hzEq
    exact hpost x hx

/-- `hybridProj` preserves the counters used by `allowCorr`. -/
private lemma allowCorr_hybridProj (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) :
    allowCorr gp (hybridProj (F := F) (gen := gen) gp a b s) = allowCorr gp s := by
  rfl

/-- `hybridProj` preserves the counters used by `finishedA`. -/
private lemma finishedA_hybridProj (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) :
    finishedA gp (hybridProj (F := F) (gen := gen) gp a b s) = finishedA gp s := by
  rfl

/-- `hybridProj` preserves the counters used by `finishedB`. -/
private lemma finishedB_hybridProj (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) :
    finishedB gp (hybridProj (F := F) (gen := gen) gp a b s) = finishedB gp s := by
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- With `ΔCKA = 1`, `corruptA` can never occur while `tA = tStar`. -/
private lemma tA_ne_tStar_of_corruptA_allowed
    (gp : GameParams) (s : GameState (F ⊕ G) G G)
    (hΔ : gp.deltaCKA = 1)
    (hallow : allowCorr gp s || finishedA gp s = true) :
    s.tA ≠ gp.tStar := by
  intro htA
  have hcases : allowCorr gp s = true ∨ finishedA gp s = true := by
    simpa [Bool.or_eq_true_eq_eq_true_or_eq_true] using hallow
  rcases hcases with hcorr | hfin
  · have hcorr' : max s.tA s.tB + 2 ≤ gp.tStar := by
      simpa [allowCorr] using hcorr
    omega
  · have hfin' : gp.tStar + 1 ≤ s.tA := by
      simpa [finishedA, finishedP, hΔ] using hfin
    omega

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- With `ΔCKA = 1`, `corruptB` can never occur while `tB = tStar - 1`. -/
private lemma tB_ne_tStar_sub_one_of_corruptB_allowed
    (gp : GameParams) (s : GameState (F ⊕ G) G G)
    (hΔ : gp.deltaCKA = 1)
    (hallow : allowCorr gp s || finishedB gp s = true) :
    s.tB ≠ gp.tStar - 1 := by
  intro htB
  have hcases : allowCorr gp s = true ∨ finishedB gp s = true := by
    simpa [Bool.or_eq_true_eq_eq_true_or_eq_true] using hallow
  rcases hcases with hcorr | hfin
  · have hcorr' : max s.tA s.tB + 2 ≤ gp.tStar := by
      simpa [allowCorr] using hcorr
    omega
  · have hfin' : gp.tStar + 1 ≤ s.tB := by
      simpa [finishedB, finishedP, hΔ] using hfin
    omega

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- With `ΔCKA = 1`, `corruptB` can never occur while `tB = tStar`. -/
private lemma tB_ne_tStar_of_corruptB_allowed
    (gp : GameParams) (s : GameState (F ⊕ G) G G)
    (hΔ : gp.deltaCKA = 1)
    (hallow : allowCorr gp s || finishedB gp s = true) :
    s.tB ≠ gp.tStar := by
  intro htB
  have hcases : allowCorr gp s = true ∨ finishedB gp s = true := by
    simpa [Bool.or_eq_true_eq_eq_true_or_eq_true] using hallow
  rcases hcases with hcorr | hfin
  · have hcorr' : max s.tA s.tB + 2 ≤ gp.tStar := by
      simpa [allowCorr] using hcorr
    omega
  · have hfin' : gp.tStar + 1 ≤ s.tB := by
      simpa [finishedB, finishedP, hΔ] using hfin
    omega

/-- With `ΔCKA = 1`, the A-state projection window closes before `corruptA`
can return a state. -/
private lemma hybridProj_stA_eq_of_corruptA_allowed
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hΔ : gp.deltaCKA = 1)
    (hallow : allowCorr gp s || finishedA gp s = true) :
    (hybridProj (F := F) (gen := gen) gp a b s).stA = s.stA := by
  have htA : s.tA ≠ gp.tStar :=
    tA_ne_tStar_of_corruptA_allowed (F := F) gp s hΔ hallow
  cases hcp : gp.challengedParty <;> cases hsA : s.stA <;>
    simp [hybridProj, hcp, hsA, htA]

/-- With `ΔCKA = 1`, the B-state projection window closes before `corruptB`
can return a state. -/
private lemma hybridProj_stB_eq_of_corruptB_allowed
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (hΔ : gp.deltaCKA = 1)
    (hallow : allowCorr gp s || finishedB gp s = true) :
    (hybridProj (F := F) (gen := gen) gp a b s).stB = s.stB := by
  cases hcp : gp.challengedParty
  · have htB : s.tB ≠ gp.tStar - 1 :=
      tB_ne_tStar_sub_one_of_corruptB_allowed (F := F) gp s hΔ hallow
    cases hsB : s.stB <;> simp [hybridProj, hcp, hsB, htB]
  · have htB : s.tB ≠ gp.tStar :=
      tB_ne_tStar_of_corruptB_allowed (F := F) gp s hΔ hallow
    cases hsB : s.stB <;> simp [hybridProj, hcp, hsB, htB]

/-- `corruptA` preserves `hybridRel` once `ΔCKA = 1` is made explicit:
the projection no longer changes the returned A-state when corruption is legal,
and otherwise both sides return `none` while keeping the same states. -/
private lemma hybridRel_query_corruptA
    (gp : GameParams) (a b : F) (sR sH : GameState (F ⊕ G) G G)
    (hΔ : gp.deltaCKA = 1)
    (hrel : hybridRel (F := F) (G := G) (gen := gen) gp a b sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleCorruptA gp (F ⊕ G) G G ()).run sR)
      ((oracleCorruptA gp (F ⊕ G) G G ()).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  rcases hrel with ⟨rfl, hInv, hWin⟩
  by_cases hallow : allowCorr gp sR = true ∨ finishedA gp sR = true
  · have hallowBool : allowCorr gp sR || finishedA gp sR = true := by
      simpa [Bool.or_eq_true_eq_eq_true_or_eq_true] using hallow
    have hallowH : allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR) = true ∨
        finishedA gp (hybridProj (F := F) (gen := gen) gp a b sR) = true := by
      simpa [allowCorr_hybridProj, finishedA_hybridProj] using hallow
    have hstA := hybridProj_stA_eq_of_corruptA_allowed
      (F := F) (gen := gen) gp a b sR hΔ hallowBool
    simpa [oracleCorruptA, hallow, hallowH, hstA] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := (some sR.stA, sR))
        (b := (some sR.stA, hybridProj (F := F) (gen := gen) gp a b sR))
        ⟨rfl, ⟨rfl, hInv, hWin⟩⟩)
  · have hallowH : ¬(allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR) = true ∨
        finishedA gp (hybridProj (F := F) (gen := gen) gp a b sR) = true) := by
      simpa [allowCorr_hybridProj, finishedA_hybridProj] using hallow
    simpa [oracleCorruptA, hallow, hallowH] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun (pR pH : Option (F ⊕ G) × GameState (F ⊕ G) G G) =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := ((none : Option (F ⊕ G)), sR))
        (b := ((none : Option (F ⊕ G)), hybridProj (F := F) (gen := gen) gp a b sR))
        ⟨rfl, ⟨rfl, hInv, hWin⟩⟩)

/-- Symmetric corruption leaf for `corruptB`. -/
private lemma hybridRel_query_corruptB
    (gp : GameParams) (a b : F) (sR sH : GameState (F ⊕ G) G G)
    (hΔ : gp.deltaCKA = 1)
    (hrel : hybridRel (F := F) (G := G) (gen := gen) gp a b sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleCorruptB gp (F ⊕ G) G G ()).run sR)
      ((oracleCorruptB gp (F ⊕ G) G G ()).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  rcases hrel with ⟨rfl, hInv, hWin⟩
  by_cases hallow : allowCorr gp sR = true ∨ finishedB gp sR = true
  · have hallowBool : allowCorr gp sR || finishedB gp sR = true := by
      simpa [Bool.or_eq_true_eq_eq_true_or_eq_true] using hallow
    have hallowH : allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR) = true ∨
        finishedB gp (hybridProj (F := F) (gen := gen) gp a b sR) = true := by
      simpa [allowCorr_hybridProj, finishedB_hybridProj] using hallow
    have hstB := hybridProj_stB_eq_of_corruptB_allowed
      (F := F) (gen := gen) gp a b sR hΔ hallowBool
    simpa [oracleCorruptB, hallow, hallowH, hstB] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := (some sR.stB, sR))
        (b := (some sR.stB, hybridProj (F := F) (gen := gen) gp a b sR))
        ⟨rfl, ⟨rfl, hInv, hWin⟩⟩)
  · have hallowH : ¬(allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR) = true ∨
        finishedB gp (hybridProj (F := F) (gen := gen) gp a b sR) = true) := by
      simpa [allowCorr_hybridProj, finishedB_hybridProj] using hallow
    simpa [oracleCorruptB, hallow, hallowH] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun (pR pH : Option (F ⊕ G) × GameState (F ⊕ G) G G) =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := ((none : Option (F ⊕ G)), sR))
        (b := ((none : Option (F ⊕ G)), hybridProj (F := F) (gen := gen) gp a b sR))
        ⟨rfl, ⟨rfl, hInv, hWin⟩⟩)

end hybridHelpers

/-- One-step relational property for the real/hybrid bridge.

This is the right local statement for `securityReduction_real_to_hybrid`:
the bridge only needs to hold on related reachable states, not on arbitrary game states. -/
private lemma hybridRel_query (gp : GameParams) (hΔ : gp.deltaCKA = 1) (a b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (sR sH : GameState (F ⊕ G) G G)
    (hrel : hybridRel (F := F) (G := G) (gen := gen) gp a b sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      (((reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen)) t).run sR)
      (((hybridOracleImpl (F := F) gp gen a b) t).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  cases_oracle t
  -- unif
  · exact hybridRel_query_unif (F := F) (G := G) (gen := gen) gp a b t sR sH hrel
  -- sendA: at embedding epoch, reduction samples fresh y for stA while hybrid uses a;
  -- outputs (aG, xB·aG) agree, hybridProj absorbs the stA difference
  · sorry
  -- recvA: both sides run oracleRecvA; hybridProj does not change stA at recvA-reachable
  -- states (stA = .inl y after a preceding sendA/challA), so recv sees the same stA
  · rcases hrel with ⟨rfl, hInv, hWin⟩
    cases hstep : validStep sR.lastAction .recvA
    · have hstepH :
          validStep (hybridProj (F := F) (gen := gen) gp a b sR).lastAction .recvA = false := by
        simpa [hybridProj] using hstep
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((oracleRecvA (ddhCKA F G gen) ()).run sR)
        ((oracleRecvA (ddhCKA F G gen) ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      have hrunL :
          ((oracleRecvA (ddhCKA F G gen) ()).run sR) = pure ((), sR) := by
        simp [oracleRecvA, hstep, StateT.run_bind, StateT.run_get, pure_bind]
      have hrunH :
          ((oracleRecvA (ddhCKA F G gen) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR)) =
            pure ((), hybridProj (F := F) (gen := gen) gp a b sR) := by
        simp [oracleRecvA, hstepH, StateT.run_bind, StateT.run_get, pure_bind]
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((), sR))
          (b := ((), hybridProj (F := F) (gen := gen) gp a b sR))
          ⟨rfl, ⟨rfl, hInv, hWin⟩⟩)
    · cases hact : sR.lastAction with
      | none =>
          exfalso; simp [hact, validStep] at hstep
      | some act =>
          cases act with
          | sendA => exfalso; simp [hact, validStep] at hstep
          | recvA => exfalso; simp [hact, validStep] at hstep
          | recvB => exfalso; simp [hact, validStep] at hstep
          | challA => exfalso; simp [hact, validStep] at hstep
          -- In the divergence window, hybridProj may set stA := .inl a/b,
          -- causing hybrid recv to compute a different key than reduction recv.
          -- This would set sH_new.correct := false, violating reachableInv.
          -- Resolution requires extending hybridProj to also track lastKeyB,
          -- or weakening hybridRel to allow correct differences.
          | sendB => sorry
          | challB => sorry
  -- sendB: symmetric to sendA for the challenged-A case
  · sorry
  -- recvB: symmetric to recvA; hybridProj does not change stB at recvB-reachable states
  · rcases hrel with ⟨rfl, hInv, hWin⟩
    cases hstep : validStep sR.lastAction .recvB
    · have hstepH :
          validStep (hybridProj (F := F) (gen := gen) gp a b sR).lastAction .recvB = false := by
        simpa [hybridProj] using hstep
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((oracleRecvB (ddhCKA F G gen) ()).run sR)
        ((oracleRecvB (ddhCKA F G gen) ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      have hrunL :
          ((oracleRecvB (ddhCKA F G gen) ()).run sR) = pure ((), sR) := by
        simp [oracleRecvB, hstep, StateT.run_bind, StateT.run_get, pure_bind]
      have hrunH :
          ((oracleRecvB (ddhCKA F G gen) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR)) =
            pure ((), hybridProj (F := F) (gen := gen) gp a b sR) := by
        simp [oracleRecvB, hstepH, StateT.run_bind, StateT.run_get, pure_bind]
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((), sR))
          (b := ((), hybridProj (F := F) (gen := gen) gp a b sR))
          ⟨rfl, ⟨rfl, hInv, hWin⟩⟩)
    · cases hact : sR.lastAction with
      | none =>
          exfalso; simp [hact, validStep] at hstep
      | some act =>
          cases act with
          | recvA => exfalso; simp [hact, validStep] at hstep
          | sendB => exfalso; simp [hact, validStep] at hstep
          | recvB => exfalso; simp [hact, validStep] at hstep
          | challB => exfalso; simp [hact, validStep] at hstep
          -- Symmetric window-divergence issue as in the recvA case.
          | sendA => sorry
          | challA => sorry
  -- challA: reduction uses (gB, gT) with stA := z; hybrid uses (b·G, ab·G) with stA := b;
  -- outputs agree since gB = b·gen and gT = (a*b)·gen; hybridWindowInv tracks the window
  · sorry
  -- challB: symmetric to challA for the challenged-B case
  · sorry
  -- corruptA
  · exact hybridRel_query_corruptA (F := F) (G := G) (gen := gen) gp a b sR sH hΔ hrel
  -- corruptB
  · exact hybridRel_query_corruptB (F := F) (G := G) (gen := gen) gp a b sR sH hΔ hrel

/-- First half of the real-branch bridge: the concrete reduction may differ from
`hybridOracleImpl` on hidden intermediate state, but these differences remain
unobservable under the healing predicate (`ΔCKA = 1`). -/
private lemma securityReduction_real_to_hybrid (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] =
    Pr[= false | securityHybridGame (gen := gen) gp adversary] := by
  unfold securityReductionRealGame securityHybridGame
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro a
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro b
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro x₀
  have hrel_init :=
    hybridRel_init (F := F) (G := G) (gen := gen) gp a b x₀
  have hrun' :=
    OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run'
      (impl₁ := reductionOracleImpl gp gen (a • gen) (b • gen) ((a * b) • gen))
      (impl₂ := hybridOracleImpl (F := F) gp gen a b)
      (R_state := hybridRel (F := F) (G := G) (gen := gen) gp a b)
      adversary
      (himpl := hybridRel_query (F := F) (G := G) (gen := gen) gp hΔ a b)
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      hrel_init
  exact OracleComp.ProgramLogic.Relational.probOutput_eq_of_relTriple_eqRel hrun' false

/-- Second half of the real-branch bridge: `hybridOracleImpl` is the honest
fixed-bit-false game with the two special challenge scalars sampled explicitly
up front.

**Proof strategy.** The hybrid samples `a, b ← $F` up front and uses each exactly
once (at the embedding send and challenge epochs respectively), whereas the honest
game samples fresh scalars on demand. Since each external scalar is uniform and
used at most once, eager sampling (hybrid) and lazy sampling (honest) produce the
same marginal distribution. Formally this follows from `probOutput_bind_bind_swap`
to commute the external samples past the `simulateQ` induction, together with
`probOutput_bind_bijective_uniform_cross` (identity bijection) at the two embedding
steps to absorb `a` into the honest oracle's `y ← $F` and `b` into `x ← $F`. -/
private lemma securityReduction_hybrid_to_honest (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityHybridGame (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  sorry

/-- The core bridge for the real branch: the explicit real-DDH reduction game
matches the explicit fixed-bit CKA game with `b = false`. -/
private lemma securityReduction_real_bridge (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  rw [securityReduction_real_to_hybrid (gen := gen) gp hΔ adversary]
  exact securityReduction_hybrid_to_honest (gen := gen) gp hΔ adversary

/-- **Real-branch lemma.**
`Pr[ℬ outputs true | real DDH] = Pr[𝒜 guesses false | CKA b = false]`. -/
lemma securityReduction_real (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  rw [probOutput_ddhExpReal_securityReduction, probOutput_securityExpFixedBit_false]
  exact securityReduction_real_bridge (gen := gen) gp hΔ adversary

/-- **Random-branch lemma.**
`Pr[ℬ outputs true | random DDH] = Pr[𝒜 guesses false | CKA b = true]`.
Needs bijectivity of `· • gen` to couple `c • gen` with `$ᵗ G`. -/
lemma securityReduction_rand (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpRand gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true gp] := by
  sorry

/-! ### Main security theorems

From the branch lemmas `securityReduction_real` and `securityReduction_rand`,
together with the fair-coin decomposition of both games:

  `Pr[DDH win] - 1/2 = (Pr[ℬ=1|real] - Pr[ℬ=1|rand]) / 2`
                      `= (Pr[𝒜=0|b=0] - Pr[𝒜=0|b=1]) / 2`
                      `= Pr[CKA win] - 1/2`

Hence `ddhGuessAdvantage(gen, ℬ) = securityAdvantage(ddhCKA, 𝒜, gp)`.
-/

/-- **DDH-CKA security (per-adversary form)** [ACD19, Theorem 3].

For any CKA adversary `𝒜`, the CKA advantage is bounded by the DDH
guess-advantage of the reduction `ℬ = securityReduction gp 𝒜`:

  `securityAdvantage(ddhCKA, 𝒜, gp) ≤ ddhGuessAdvantage(gen, ℬ)` -/
theorem security (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    securityAdvantage (ddhCKA F G gen) adversary gp ≤
      ddhGuessAdvantage gen (securityReduction gp adversary) := by
  sorry

/-- **DDH-CKA security (quantitative form)** [ACD19, Theorem 3].

If the DDH assumption holds in `G` with guess-advantage at most `ε` for every
adversary, then for any CKA adversary `𝒜`:

  `securityAdvantage(ddhCKA, 𝒜, gp) ≤ ε` -/
theorem ddhCKA_security (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G)
    (ε : ℝ)
    (hddh : ∀ adv : DDHAdversary F G,
      ddhGuessAdvantage gen adv ≤ ε) :
    securityAdvantage (ddhCKA F G gen) adversary gp ≤ ε :=
  calc securityAdvantage (ddhCKA F G gen) adversary gp
      ≤ ddhGuessAdvantage gen (securityReduction gp adversary) :=
        security gp hΔ hg adversary
    _ ≤ ε := hddh _

end ddhCKA

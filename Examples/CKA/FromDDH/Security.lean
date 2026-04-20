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

Goal: `𝒜`'s view in the CKA game equals its view in the reduction's simulation.
The reduction `ℬ` returns `¬b'`, so the top-level branch identities are:

    Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA^{b = false}]   … (**real branch**)
    Pr[ℬ = true | DDH_rand] = Pr[𝒜 = false | CKA^{b = true }]   … (**random branch**)

Each branch is proved by a chain of distribution-preserving rewrites through a
sequence of explicit "helper games" — one-shot `ProbComp Bool` definitions that
wrap `simulateQ adversary` under a specific oracle implementation.

#### Real branch: 4-step chain through 3 helper games

```text
┌───────────────────────────────────┐
│  Pr[ℬ = true | DDH_real]          │
└───────────────────────────────────┘
               ║   (1) Lemma probOutput_ddhExpReal_securityReduction:
               ║          Pr[ℬ = true | DDH_real] = Pr[G_R = false]
               ║       Proof: ℬ returns `!b'`, so `probOutput_not_map` pulls the
               ║        `= true` event back to `= false` under `G_R`
               ▼
┌───────────────────────────────────┐   G_R := securityReductionRealGame
│  Pr[G_R   = false]                │         𝒜 vs `reductionOracleImpl g aG bG (ab)G`
└───────────────────────────────────┘
               ║   (2) Lemma securityReduction_real_to_hybrid:
               ║          Pr[G_R = false] = Pr[G_H = false]
               ║       Proof: relational Hoare (`RelTriple`) with invariant
               ║        `hybridRel` and state projection `hybridProj`;
               ║        hidden-state differences at the embedding epochs
               ║        are unobservable
               ▼
┌───────────────────────────────────┐   G_H := securityHybridGame
│  Pr[G_H   = false]                │         𝒜 vs `hybridOracleImpl g a b`
└───────────────────────────────────┘
               ║   (3) Lemma securityReduction_hybrid_to_honest:
               ║          Pr[G_H = false] = Pr[G_CKA = false]
               ║       Proof: eager-vs-lazy sampling equivalence —
               ║        `probOutput_bind_bind_swap` commutes the up-front
               ║        `a, b ← $F` past `simulateQ`, then
               ║        `probOutput_bind_bijective_uniform_cross` at the two
               ║        embedding steps absorbs them into the honest oracle's
               ║        lazy samples
               ▼
┌───────────────────────────────────┐   G_CKA := securityExpFixedBitFalseGame
│  Pr[G_CKA = false]                │         𝒜 vs `ckaSecurityImpl` (honest)
└───────────────────────────────────┘
               ║   (4) Lemma probOutput_securityExpFixedBit_false:
               ║          Pr[G_CKA = false] = Pr[𝒜 = false | CKA^{b = false}]
               ║       Proof: definitional unfolding of `securityExpFixedBit`
               ▼
┌───────────────────────────────────┐
│  Pr[𝒜 = false | CKA^{b = false}]  │
└───────────────────────────────────┘
```

Each step is a standalone lemma. The full four-step chain
`Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA^{b = false}]` is assembled in
`securityReduction_real`. The three helper
games correspond to the three oracle-impl columns in the diagram at the top
of the file:

- `G_R` := `securityReductionRealGame`
  - oracles: `reductionOracleImpl g (a•gen) (b•gen) ((a*b)•gen)`
  - role: entry point for the DDH reduction
- `G_H` := `securityHybridGame`
  - oracles: `hybridOracleImpl g a b`
  - role: hidden-state bridge; same outputs as `G_R`
- `G_CKA` := `securityExpFixedBitFalseGame`
  - oracles: `ckaSecurityImpl g (ddhCKA F G gen)`
  - role: honest CKA with `b = false`

`G_H` is the crucial intermediate: `G_R` and `G_H` produce **identical
observable transcripts** (they differ only on hidden party state, which
`hybridProj` absorbs), while `G_H` and `G_CKA` have **identical output
distributions** but different control flow (eager up-front sampling of
`a, b ← $F` vs. lazy on-demand sampling).

-/

/-- Auxiliary game `G_R(𝒜)`: samples `a, b, x₀ ← $F`, runs `𝒜` against
`R := reductionOracleImpl(g, a•gen, b•gen, (a*b)•gen)`, and returns `b'`
(i.e. without the final `¬·` applied by the reduction
`ℬ := securityReduction`).

Entry point to the real-branch chain: step (2)
`securityReduction_real_to_hybrid` rewrites `G_R` into `G_H`. -/
private noncomputable def securityReductionRealGame (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : ProbComp Bool := do
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
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRealGame (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpReal securityReduction
  simpa [securityReductionRealGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRealGame (gen := gen) gp adversary))

/-- Auxiliary game `G_CKA(𝒜)`: samples only `x₀ ← $F` up front and runs `𝒜`
against the honest CKA implementation `ckaSecurityImpl gp (ddhCKA F G gen)`,
with the fixed challenge bit `b = false` baked into the initial state.

Unlike `G_R` / `G_H`, the external scalars `a, b` are **not** sampled up
front here: the honest game samples fresh scalars lazily on each oracle
call (at the `sendA`/`sendB`/`challA`/`challB` embedding epochs).

Named endpoint game for the real-branch chain.

Write

- `G_R := securityReductionRealGame gp adversary`,
- `G_H := securityHybridGame gp adversary`,
- `G_CKA := securityExpFixedBitFalseGame gp adversary`.

The bridge lemmas are organized as

  `G_R  ->  G_H  ->  G_CKA`

before the final definitional fold back to the generic notation
`securityExpFixedBit (ddhCKA F G gen) adversary false gp`. Thus this helper
appears here, near the real-branch bridge, rather than later in the final
theorem section. -/
private noncomputable def securityExpFixedBitFalseGame (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl gp (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
  return b'

/-- **Step (4) of the real branch.** Fold the named endpoint game `G_CKA`
back into the generic fixed-bit notation at `b = false`:
ok
  `Pr[𝒜 = false ∣ CKA^{b = false}]  =  Pr[G_CKA = false]`

where `G_CKA := securityExpFixedBitFalseGame gp 𝒜`. This is a pure
definitional unfolding of `securityExpFixedBit` at `ddhCKA F G gen` —
no probabilistic content, just an `unfold`/`simp` on the generic game
shape exposing the initial key sample `x₀ ← $F`. -/
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

/-- Projection `π : GameState → GameState` used in the local coupling between
`R := reductionOracleImpl(g, aG, bG, abG)` and `H := hybridOracleImpl(g, a, b)`.

### Notation

Throughout this docstring (and reused by the sibling invariants
`hybridWindowInv`, `hybridShapeInv`, `hybridRel`):

- A party's local state `stA`, `stB : F ⊕ G` is either a **scalar-state**
  `.inl x` carrying a field element `x : F`, or a **G-state** `.inr g` carrying
  a group element `g : G`.
- `gen : G` is the protocol's fixed generator; `aG := a • gen`, `bG := b • gen`.
- `t* := gp.tStar` is the challenge epoch and `P := gp.challengedParty` is the
  challenged party.

### What `π` does

Given a reduction-side state `S_R`, `π` produces the matching hybrid-side state
by overwriting each party's hidden scalar inside the **challenge window** with
the DDH scalar that the hybrid would have stored there — everything else passes
through unchanged.

### The rewrite pattern

Write `P := gp.challengedParty` and `t* := gp.tStar`. Only `stA` and `stB` are
ever rewritten, and only when they carry an `.inl _` scalar (the `.inr _`
G-state case is always identity). The pattern is symmetric in the two parties:

| `P` | `stA` rewrite target | `stB` rewrite target |
|-----|----------------------|----------------------|
| `A` | `.inl b`             | `.inl a`             |
| `B` | `.inl a`             | `.inl b`             |

Intuition:
- The *challenged* party's scalar becomes `b` — the **challenge scalar**, whose
  image `bG` appears as the challenge message.
- The *other* party's scalar becomes `a` — the **pre-challenge embedding
  scalar**, whose image `aG` appears as the last message before the challenge.

### When each rewrite fires

The four match-arms in full (each bullet contributes one disjunct to the
guard). See the observations block afterwards for the three ways in which the
cases differ beyond a party-name swap.

**(1) `(P = A, stA = .inl _) → .inl b`** — all disjuncts also require `tA = t*`:
- `lastAction = challA`.
- `lastAction = recvB`  and  `stB = .inr (b • gen)`.
- `lastAction = sendB`  and  `tB = t* + 1`.

**(2) `(P = B, stA = .inl _) → .inl a`** — all disjuncts also require `tA = t*`:
- `lastAction = sendA`.
- `lastAction = recvB`  and  `stB = .inr (a • gen)`.
- `lastAction = sendB`   and  `sent = true`.
- `lastAction = challB`  and  `sent = true`.

**(3) `(P = A, stB = .inl _) → .inl a`** — all disjuncts also require `tB = t* - 1`:
- `lastAction = sendB`.
- `lastAction = recvA`.
- `lastAction = sendA`   and  `sent = true`.
- `lastAction = challA`  and  `sent = true`.

**(4) `(P = B, stB = .inl _) → .inl b`** — all disjuncts also require `tB = t*`:
- `lastAction = challB`.
- `lastAction = recvA`.
- `lastAction = sendA`.

Observations:
- The **challenged party's own state** (cases 1, 4) never consults `sent`; the
  `lastAction` and counter are already enough to pin down the challenge
  post-state.
- The **other party's state** (cases 2, 3) uses `sent` on exactly the two
  clauses where the `lastAction` alone would be ambiguous.
- The peer-state image check (`stB = .inr (b • gen)` in case 1 vs.
  `stB = .inr (a • gen)` in case 2) flips between the **challenge** message
  `bG` (when P = A, so B received B's own challenge draft as the peer read)
  and the **embedding** message `aG` (when P = B, so A received the embedded
  send from B before B's challenge).
- The counter guards `tA = t*` vs `tB = t* - 1` reflect the protocol: A sends
  first, so when B is mid-epoch at `tB = t* - 1` (just before its own
  challenge), A is already at `tA = t*`.

### The `sent` parameter

`sent : Bool` is a **provenance flag** consulted on exactly the four clauses
marked above (`sendB`/`challB` in case 2, `sendA`/`challA` in case 3):

- `sent = true`  → the pre-challenge embedding send has already fired, so the
                   peer-side `.inl _` now on `S_R` originates from it and must
                   be projected to `a`.
- `sent = false` → the embedding has not happened yet, so peer-side `.inl _`
                   scalars are unrelated to `a` and `π` leaves them alone.

Every state component other than `stA` and `stB` is copied through unchanged. -/
private noncomputable def hybridProj (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) (sent : Bool := false) : GameState (F ⊕ G) G G :=
  { s with
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
               (sent && (s.lastAction = some .sendB ||
                 s.lastAction = some .challB)))
          then (.inl a : F ⊕ G)
          else s.stA
      | _, .inr _ => s.stA
    stB := match gp.challengedParty, s.stB with
      | .A, .inl _ =>
          if s.tB == gp.tStar - 1 &&
              (s.lastAction = some .sendB ||
               s.lastAction = some .recvA ||
               (sent && (s.lastAction = some .sendA ||
                 s.lastAction = some .challA)))
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

/-- Window predicate for the coupling `S_H = hybridProj gp a b S_R`.

### What `W` records

On exactly the four challenge-window `(party, lastAction)` configurations,
`W(S_R)` asserts the DDH equalities that `hybridProj` needs in order to
reconstruct the hybrid transcript from the reduction state; everywhere else it
is trivially `True`.

### Case table

Write `P := gp.challengedParty`, `t* := gp.tStar`, and
`W(S_R) := hybridWindowInv gp a b S_R`:

| `(P, lastAction)` | Assertion (under the counter guard)                                                    |
|-------------------|----------------------------------------------------------------------------------------|
| `(A, challA)`     | `tA = t* → lastRhoA = b • gen ∧ lastKeyA = (a * b) • gen`                              |
| `(A, recvB)`      | `tA = t* → stB = .inr (b • gen)`                                                       |
| `(B, challB)`     | `tB = t* → lastRhoB = b • gen ∧ lastKeyB = (a * b) • gen`                              |
| `(B, recvA)`      | `tB = t* → stA = .inr (b • gen)`                                                       |
| any other         | `True`                                                                                 |

Intuition:
- `challP` rows pin the challenger's DDH transcript `(b • gen, (a * b) • gen)`.
- `recv` rows pin the peer's received challenge `b • gen` as a G-state.

Each row is guarded by `tA = t*` or `tB = t*`; outside the challenge window
the implication is vacuous. (State/scalar notation as in `hybridProj`.) -/
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

/-- Hybrid-side shape invariant for the local bridge.

### What it asserts

`hybridShapeInv(S_H)` holds iff `S_H` is honestly reachable, or is one of the
two special `challA`/`challB` post-states where the hybrid has committed the
DDH transcript `(b • gen, (a * b) • gen)` ahead of the peer's embedding send.

### The three disjuncts

Let `P := gp.challengedParty` and `t* := gp.tStar`. Then `hybridShapeInv(S_H)`
holds iff at least one of:

1. **Honest reachable shape.** `reachableShape gen S_H` — the standard shape
   invariant inherited from the honest game; covers every non-challenge state.

2. **Special `challA` post-state** (only when `P = A`). Characterised by
   - `lastAction = challA`, `(tA, tB) = (t*, t* - 1)`;
   - `stA = .inl b`, `stB = .inl x` for some `x : F`;
   - `lastRhoA = b • gen`, `lastKeyA = (a * b) • gen`;
   - `lastRhoB = none`, `lastKeyB = none`.

3. **Special `challB` post-state** (only when `P = B`). Symmetric:
   - `lastAction = challB`, `(tA, tB) = (t* - 1, t*)`;
   - `stA = .inl x`, `stB = .inl b` for some `x : F`;
   - `lastRhoB = b • gen`, `lastKeyB = (a * b) • gen`;
   - `lastRhoA = none`, `lastKeyA = none`.

Disjuncts 2–3 exactly match the range of `hybridProj` on the reduction's
challenge states, which lie just outside the honest reachable-shape image. -/
private def hybridShapeInv (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) : Prop :=
  reachableShape gen s ∨
    (gp.challengedParty = .A ∧
      s.lastAction = some .challA ∧
      s.tA = gp.tStar ∧
      s.tB = gp.tStar - 1 ∧
      ∃ x : F, s.stA = (.inl b : F ⊕ G) ∧ s.stB = (.inl x : F ⊕ G) ∧
        s.lastRhoA = some (b • gen) ∧ s.lastRhoB = none ∧
        s.lastKeyA = some ((a * b) • gen) ∧ s.lastKeyB = none) ∨
    (gp.challengedParty = .B ∧
      s.lastAction = some .challB ∧
      s.tA = gp.tStar - 1 ∧
      s.tB = gp.tStar ∧
      ∃ x : F, s.stA = (.inl x : F ⊕ G) ∧ s.stB = (.inl b : F ⊕ G) ∧
        s.lastRhoA = none ∧ s.lastRhoB = some (b • gen) ∧
        s.lastKeyA = none ∧ s.lastKeyB = some ((a * b) • gen))

/-
Notation for the bridge below:
- `S_R` is the concrete reduction state.
- `S_H` is the corresponding hybrid state, obtained from `S_R` by `hybridProj`.
- `hybridWindowInv` marks the brief post-challenge interval where the two games may
  disagree internally, while still exposing the same oracle outputs.
-/

/-- Relational invariant between reduction and hybrid states.

### What it says (one sentence)

A reduction state `S_R` and a hybrid state `S_H` are related iff `S_H` is the
image of `S_R` under `hybridProj` (for some provenance bit `sent`), `S_H` has
a valid hybrid shape, and `S_R` satisfies the window predicate justifying that
projection.

### The three conjuncts

`hybridRel gp a b S_R S_H := ∃ sent : Bool, ...` asserts:

| Conjunct                      | Role                                                                                           |
|-------------------------------|------------------------------------------------------------------------------------------------|
| `S_H = hybridProj ... sent`   | Defines the coupling: `S_H` is `S_R` with scalar rewrites in the challenge window.             |
| `hybridShapeInv gp a b S_H`   | Hybrid-side structural invariant: `reachableShape` ∪ two special `challA`/`challB` post-states. |
| `hybridWindowInv gp a b S_R`  | Reduction-side bookkeeping: on the four challenge-window configurations, fixes the DDH values. |

The existential over `sent : Bool` lets the relation absorb the pre-challenge
embedding send: before the send, `sent = false` leaves peer-side scalars alone;
after it, `sent = true` projects them onto `a`. -/
private def hybridRel (gp : GameParams) (a b : F)
    (sR sH : GameState (F ⊕ G) G G) : Prop :=
  ∃ sent : Bool,
    sH = hybridProj (F := F) (gen := gen) gp a b sR sent ∧
    hybridShapeInv (F := F) (G := G) (gen := gen) gp a b sH ∧
    hybridWindowInv (F := F) (G := G) (gen := gen) gp a b sR

/-! ### `StateProjection` refactor — draft definitions

Replaces the existential `∃ sent : Bool, …` in `hybridRel` by a pure state
function `inferSent : GameParams → GameState → Bool` that reconstructs the
provenance bit from `(gp, s)`. With `isOtherSendBeforeChall` now symmetric
(`tP other == tStar - 1`), both sides of the embedding fire on reachable
trajectories with clean parity, and `sent` becomes a pure function of
`(gp, s)`.

Key formula (both branches of the A↔B mirror):

```text
inferSent gp s  :=
  let tOther := s.tP gp.challengedParty.other
  match gp.challengedParty with
  | .A => decide (Odd  gp.tStar ∧ gp.tStar ≥ 3 ∧ tOther ≥ gp.tStar - 1)
  | .B => decide (Even gp.tStar ∧ gp.tStar ≥ 2 ∧ tOther ≥ gp.tStar - 1)
```

Correctness intuition (P = A; P = B symmetric):
- Reachable `t*` odd ≥ 3 and `sendB` post-`tB` ∈ {2, 4, …} even ≥ 2, so the
  embedding fires at the unique `sendB` with post-`tB = t* - 1`.
- Once post-`tB` has crossed `t* - 1`, it stays ≥ `t* - 1` on all successor
  states (counters are monotone), so `tB ≥ t* - 1` is exactly the "post-
  embedding" phase, i.e. `sent = true`.

With this, `hybridProj' gp a b s := hybridProj gp a b s (inferSent gp s)`
is a total projection suitable for
`map_run_simulateQ_eq_of_query_map_eq_inv'`. The `StateProjection`-friendly
invariant `hybridStateInv` bundles the reduction-side window witness and the
hybrid-side shape witness into a single `Prop` on reduction states.

Pending alignment: `hybridProj`'s P=B `stA` clause currently guards on
`tA == gp.tStar` (matching the old asymmetric embedding point). Under the
symmetric embedding, the post-embedding post-sendA state has `tA = tStar - 1`,
so that guard must become `tA == gp.tStar - 1` (with the lastAction list
possibly widened to cover the post-embedding-but-pre-recvA window). Similarly
for `hybridWindowInv` P=B cases. These updates, together with reproving the
P=B branches of `hybridRel_query`, are the remaining mechanical work for the
migration. -/

/-- Deterministic reconstruction of the `sent` provenance bit from
`(gp, state)`. See the section note above for the correctness argument. -/
private def inferSent (gp : GameParams) (s : GameState (F ⊕ G) G G) : Bool :=
  let tOther := s.tP gp.challengedParty.other
  match gp.challengedParty with
  | .A => decide (Odd  gp.tStar ∧ gp.tStar ≥ 3 ∧ tOther ≥ gp.tStar - 1)
  | .B => decide (Even gp.tStar ∧ gp.tStar ≥ 2 ∧ tOther ≥ gp.tStar - 1)

/-- Totalised `hybridProj`: threads the state-derived provenance bit
`inferSent gp s` through `hybridProj`, giving a pure function
`GameState → GameState` suitable for `map_run_simulateQ_eq_of_query_map_eq_inv'`. -/
private noncomputable def hybridProj' (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) : GameState (F ⊕ G) G G :=
  hybridProj (F := F) (gen := gen) gp a b s (inferSent gp s)

/-- Combined invariant on reduction states for the `StateProjection` refactor:
the reduction state satisfies the window witness, and its projection under
`hybridProj'` satisfies the hybrid-side shape invariant. -/
private def hybridStateInv (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) : Prop :=
  hybridWindowInv (F := F) (G := G) (gen := gen) gp a b s ∧
    hybridShapeInv (F := F) (G := G) (gen := gen) gp a b
      (hybridProj' (F := F) (gen := gen) gp a b s)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
     [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] in
/-- Base case for the `inferSent` sanity chain: if the opposite party's counter
is still zero then the pre-challenge embedding cannot yet have fired. Applies in
particular to `initGameState`, where `tA = tB = 0`. -/
private lemma inferSent_of_tOther_zero (gp : GameParams) (s : GameState (F ⊕ G) G G)
    (h : s.tP gp.challengedParty.other = 0) :
    inferSent (F := F) (G := G) gp s = false := by
  rcases hP : gp.challengedParty with _ | _ <;>
    · simp only [CKAParty.other, GameState.tP, hP] at h
      simp only [inferSent, hP, decide_eq_false_iff_not, not_and, not_le,
                 GameState.tP, CKAParty.other]
      intro _ _
      omega

/-- Map a reduction-side post-state to the corresponding hybrid-side post-state. -/
private noncomputable def hybridPostMap {α : Type} (gp : GameParams) (a b : F)
    (sent : Bool) (p : α × GameState (F ⊕ G) G G) : α × GameState (F ⊕ G) G G :=
  (p.1, hybridProj (F := F) (gen := gen) gp a b p.2 sent)

section hybridHelpers
omit [Fintype F] [SampleableType F] [SampleableType G]

/-- If the projected state has the hybrid shape and the window witness holds,
then the pair `(s, hybridProj s)` satisfies `hybridRel`. -/
private lemma hybridRel_mk (gp : GameParams) (a b : F)
    (sent : Bool)
    (s : GameState (F ⊕ G) G G)
    (hShape : hybridShapeInv (F := F) (G := G) (gen := gen) gp a b
      (hybridProj (F := F) (gen := gen) gp a b s sent))
    (hWin : hybridWindowInv (F := F) (G := G) (gen := gen) gp a b s) :
    hybridRel (F := F) (G := G) (gen := gen) gp a b s
      (hybridProj (F := F) (gen := gen) gp a b s sent) :=
  ⟨sent, rfl, hShape, hWin⟩

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

/-- Shape-only version of `reachableInv_none_or_recvA`. -/
private lemma reachableShape_none_or_recvA
    (s : GameState (F ⊕ G) G G)
    (hShape : reachableShape gen s)
    (hact : s.lastAction = none ∨ s.lastAction = some .recvA) :
    ∃ x : F, s.stA = .inr (x • gen) ∧ s.stB = .inl x ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none := by
  rcases hShape with ⟨_, hshape⟩
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

/-- Shape-only version of `reachableInv_recvB`. -/
private lemma reachableShape_recvB
    (s : GameState (F ⊕ G) G G)
    (hShape : reachableShape gen s)
    (hact : s.lastAction = some .recvB) :
    ∃ y : F, s.stA = .inl y ∧ s.stB = .inr (y • gen) ∧
      s.lastRhoA = none ∧ s.lastRhoB = none ∧ s.lastKeyA = none ∧ s.lastKeyB = none := by
  rcases hShape with ⟨_, hshape⟩
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

/-- The projected initial reduction state is already an honest hybrid state. -/
private lemma hybridRel_init (gp : GameParams) (a b x₀ : F) :
    hybridRel (F := F) (G := G) (gen := gen) gp a b
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false) := by
  refine ⟨false, ?_, ?_, ?_⟩
  · cases hcp : gp.challengedParty <;> simp [hybridProj, initGameState, hcp]
  · exact Or.inl ⟨rfl, x₀, rfl, rfl, rfl, rfl, rfl, rfl⟩
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

/-- Distribution-level variant of `relTriple_of_map_eq`.

If the `evalDist` of `f <$> oa` equals the `evalDist` of `ob`, we can couple
each left sample `x` with the right sample `f x`, without needing syntactic
equality of the programs. Useful when the right-hand side has a different
syntactic form (e.g. `pure x` vs `$F >>= fun _ => pure x`) but the same
distribution. -/
private lemma relTriple_of_evalDist_map_eq
    {α β : Type} {R : α → β → Prop}
    {oa : ProbComp α} {ob : ProbComp β}
    (f : α → β)
    (hmap : evalDist (f <$> oa) = evalDist ob)
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
        _ = evalDist ob := hmap
  · intro z hz
    rcases (mem_support_bind_iff
      (evalDist oa) (fun x => (pure (x, f x) : SPMF (α × β))) z).1 hz with
      ⟨x, hx, hz'⟩
    have hzEq : z = (x, f x) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    subst hzEq
    exact hpost x hx

/-- Uniform helper for oracle branches where the two runs agree via `hybridProj`.

If running `maR` on the reduction state `sR` and `maH` on the hybrid state
`hybridProj sR` produce results related by `hybridProj` at the state component,
and both the shape and window invariants are preserved along the support, then
the `RelTriple` with `hybridRel` postcondition holds.

Applies both to oracles where `maR = maH` (shared code: `unif`, `recv*`, `corrupt*`)
and to oracles where `maR ≠ maH` but agree on outputs (non-embedding sub-cases of
`send*`/`chall*`, and the embedding sub-cases where outputs match explicitly). -/
private lemma hybridRel_of_run_eq
    {α : Type}
    (maR maH : StateT (GameState (F ⊕ G) G G) ProbComp α)
    (sR : GameState (F ⊕ G) G G) (gp : GameParams) (a b : F)
    (sentPre sentPost : Bool)
    (hrun_eq : (fun p : α × _ => (p.1, hybridProj (F := F) (gen := gen) gp a b p.2 sentPost))
        <$> maR.run sR =
      maH.run (hybridProj (F := F) (gen := gen) gp a b sR sentPre))
    (hShape_post : ∀ p ∈ support (evalDist (maR.run sR)),
      hybridShapeInv (F := F) (G := G) (gen := gen) gp a b
        (hybridProj (F := F) (gen := gen) gp a b p.2 sentPost))
    (hWin_post : ∀ p ∈ support (evalDist (maR.run sR)),
      hybridWindowInv (F := F) (G := G) (gen := gen) gp a b p.2) :
    OracleComp.ProgramLogic.Relational.RelTriple
      (maR.run sR)
      (maH.run (hybridProj (F := F) (gen := gen) gp a b sR sentPre))
      (fun pR pH => pR.1 = pH.1 ∧
        hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  refine relTriple_of_map_eq
    (f := fun p : α × _ => (p.1, hybridProj (F := F) (gen := gen) gp a b p.2 sentPost))
    hrun_eq ?_
  intro p hp
  exact ⟨rfl, sentPost, rfl, hShape_post p hp, hWin_post p hp⟩

/-- Distribution-level variant of `hybridRel_of_run_eq`.

When the reduction-side program samples internal randomness (for example `z ← $F`
in `reductionChallA`) while the hybrid side is deterministic at the same step,
the map `(p.1, hybridProj p.2 sentPost)` applied to the reduction run is only
`evalDist`-equal to the hybrid run, not syntactically equal. This version uses
`relTriple_of_evalDist_map_eq` and is the right tool for the sample-absorbing
embedding/challenge branches. -/
private lemma hybridRel_of_run_evalDist_eq
    {α : Type}
    (maR maH : StateT (GameState (F ⊕ G) G G) ProbComp α)
    (sR : GameState (F ⊕ G) G G) (gp : GameParams) (a b : F)
    (sentPre sentPost : Bool)
    (hrun_eq : evalDist
        ((fun p : α × _ =>
            (p.1, hybridProj (F := F) (gen := gen) gp a b p.2 sentPost))
          <$> maR.run sR) =
      evalDist (maH.run (hybridProj (F := F) (gen := gen) gp a b sR sentPre)))
    (hShape_post : ∀ p ∈ support (evalDist (maR.run sR)),
      hybridShapeInv (F := F) (G := G) (gen := gen) gp a b
        (hybridProj (F := F) (gen := gen) gp a b p.2 sentPost))
    (hWin_post : ∀ p ∈ support (evalDist (maR.run sR)),
      hybridWindowInv (F := F) (G := G) (gen := gen) gp a b p.2) :
    OracleComp.ProgramLogic.Relational.RelTriple
      (maR.run sR)
      (maH.run (hybridProj (F := F) (gen := gen) gp a b sR sentPre))
      (fun pR pH => pR.1 = pH.1 ∧
        hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  refine relTriple_of_evalDist_map_eq
    (f := fun p : α × _ => (p.1, hybridProj (F := F) (gen := gen) gp a b p.2 sentPost))
    hrun_eq ?_
  intro p hp
  exact ⟨rfl, sentPost, rfl, hShape_post p hp, hWin_post p hp⟩

/-- `hybridProj` preserves the counters used by `allowCorr`. -/
private lemma allowCorr_hybridProj (gp : GameParams) (a b : F)
    (sent : Bool)
    (s : GameState (F ⊕ G) G G) :
    allowCorr gp (hybridProj (F := F) (gen := gen) gp a b s sent) = allowCorr gp s := by
  rfl

/-- `hybridProj` preserves the counters used by `finishedA`. -/
private lemma finishedA_hybridProj (gp : GameParams) (a b : F)
    (sent : Bool)
    (s : GameState (F ⊕ G) G G) :
    finishedA gp (hybridProj (F := F) (gen := gen) gp a b s sent) = finishedA gp s := by
  rfl

/-- `hybridProj` preserves the counters used by `finishedB`. -/
private lemma finishedB_hybridProj (gp : GameParams) (a b : F)
    (sent : Bool)
    (s : GameState (F ⊕ G) G G) :
    finishedB gp (hybridProj (F := F) (gen := gen) gp a b s sent) = finishedB gp s := by
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
    (sent : Bool)
    (hΔ : gp.deltaCKA = 1)
    (hallow : allowCorr gp s || finishedA gp s = true) :
    (hybridProj (F := F) (gen := gen) gp a b s sent).stA = s.stA := by
  have htA : s.tA ≠ gp.tStar :=
    tA_ne_tStar_of_corruptA_allowed (F := F) gp s hΔ hallow
  cases hcp : gp.challengedParty <;> cases hsA : s.stA <;>
    simp [hybridProj, hcp, hsA, htA]

/-- With `ΔCKA = 1`, the B-state projection window closes before `corruptB`
can return a state. -/
private lemma hybridProj_stB_eq_of_corruptB_allowed
    (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G)
    (sent : Bool)
    (hΔ : gp.deltaCKA = 1)
    (hallow : allowCorr gp s || finishedB gp s = true) :
    (hybridProj (F := F) (gen := gen) gp a b s sent).stB = s.stB := by
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
  rcases hrel with ⟨sent, rfl, hInv, hWin⟩
  by_cases hallow : allowCorr gp sR = true ∨ finishedA gp sR = true
  · have hallowBool : allowCorr gp sR || finishedA gp sR = true := by
      simpa [Bool.or_eq_true_eq_eq_true_or_eq_true] using hallow
    have hallowH : allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true ∨
        finishedA gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true := by
      simpa [allowCorr_hybridProj, finishedA_hybridProj] using hallow
    have hstA := hybridProj_stA_eq_of_corruptA_allowed
      (F := F) (gen := gen) gp a b sR sent hΔ hallowBool
    simpa [oracleCorruptA, hallow, hallowH, hstA] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := (some sR.stA, sR))
        (b := (some sR.stA, hybridProj (F := F) (gen := gen) gp a b sR sent))
        ⟨rfl, ⟨sent, rfl, hInv, hWin⟩⟩)
  · have hallowH : ¬(allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true ∨
        finishedA gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true) := by
      simpa [allowCorr_hybridProj, finishedA_hybridProj] using hallow
    simpa [oracleCorruptA, hallow, hallowH] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun (pR pH : Option (F ⊕ G) × GameState (F ⊕ G) G G) =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := ((none : Option (F ⊕ G)), sR))
        (b := ((none : Option (F ⊕ G)), hybridProj (F := F) (gen := gen) gp a b sR sent))
        ⟨rfl, ⟨sent, rfl, hInv, hWin⟩⟩)

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
  rcases hrel with ⟨sent, rfl, hInv, hWin⟩
  by_cases hallow : allowCorr gp sR = true ∨ finishedB gp sR = true
  · have hallowBool : allowCorr gp sR || finishedB gp sR = true := by
      simpa [Bool.or_eq_true_eq_eq_true_or_eq_true] using hallow
    have hallowH : allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true ∨
        finishedB gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true := by
      simpa [allowCorr_hybridProj, finishedB_hybridProj] using hallow
    have hstB := hybridProj_stB_eq_of_corruptB_allowed
      (F := F) (gen := gen) gp a b sR sent hΔ hallowBool
    simpa [oracleCorruptB, hallow, hallowH, hstB] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := (some sR.stB, sR))
        (b := (some sR.stB, hybridProj (F := F) (gen := gen) gp a b sR sent))
        ⟨rfl, ⟨sent, rfl, hInv, hWin⟩⟩)
  · have hallowH : ¬(allowCorr gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true ∨
        finishedB gp (hybridProj (F := F) (gen := gen) gp a b sR sent) = true) := by
      simpa [allowCorr_hybridProj, finishedB_hybridProj] using hallow
    simpa [oracleCorruptB, hallow, hallowH] using
      (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        (spec₁ := unifSpec) (spec₂ := unifSpec)
        (R := fun (pR pH : Option (F ⊕ G) × GameState (F ⊕ G) G G) =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        (a := ((none : Option (F ⊕ G)), sR))
        (b := ((none : Option (F ⊕ G)), hybridProj (F := F) (gen := gen) gp a b sR sent))
        ⟨rfl, ⟨sent, rfl, hInv, hWin⟩⟩)

end hybridHelpers

/-- **One-step simulation lemma** for the real/hybrid coupling — the inductive
step that `securityReduction_real_to_hybrid` lifts through `simulateQ` via
relational Hoare (`RelTriple.simulateQ_run'`).

### What this lemma proves

For every single oracle query `t : ckaSecuritySpec (F ⊕ G) G G` and every pair of
pre-states `(S_R, S_H)` with `hybridRel gp a b S_R S_H`, running `t` under the two
oracle implementations

  `R := reductionOracleImpl gp gen (a•gen) (b•gen) ((a*b)•gen)`  (reduction side)
  `H := hybridOracleImpl     gp gen a b`                         (hybrid side)

yields a `RelTriple` between

  `(o_R, S_R') ← (R t).run S_R`    and    `(o_H, S_H') ← (H t).run S_H`

witnessing two facts on every joint execution:

  (A) **Observable output equality**: `o_R = o_H`. The reduction's fresh per-call
      scalars (`y ← $F` in `reductionSendA/B`; `z ← $F` in `reductionChallA/B`)
      are absorbed by `hybridProj` and never appear in the returned transcript.

  (B) **Invariant preservation**: `hybridRel gp a b S_R' S_H'`, i.e. the post-
      states remain related by the same projection `S_H' = hybridProj gp a b S_R'`
      (possibly with a new `sent` flag) together with the shape/window invariants.

Together, (A) and (B) let `RelTriple.simulateQ_run'` run the adversary `𝒜`'s
whole oracle-query tree on both sides while keeping the views identical at every
step, which is exactly the distributional equivalence needed between `G_R` and
`G_H` (see `securityReduction_real_to_hybrid`).

### Proof structure

Outer case split: `cases_oracle t` — one branch per summand of `ckaSecuritySpec`:
  * `unif`       — shared `oracleUnif` on both sides; trivial.
  * `sendA`      — diverges only at the embedding epoch (`challengedParty = .B`
                   and `tA+1 = tStar`); otherwise both sides run `ddhCKA.send`.
  * `recvA`      — `oracleRecvA` is shared code; `hybridProj` absorbs the stB
                   divergence introduced by a prior embedding `sendB`.
  * `sendB`      — symmetric to `sendA`, embedding at `challengedParty = .A`.
  * `recvB`      — symmetric to `recvA`.
  * `challA`/`challB` — diverge at the challenge epoch; `hybridProj` rewrites
                   the stA/stB reduction-scalar into `.inl b`, matching hybrid.
  * `corruptA`/`corruptB` — shared code; `hΔ : deltaCKA = 1` forbids corruption
                   during the challenge window, so the window rewrite is closed
                   before the adversary can observe it (see `hybridRel_query_corruptA/B`).

Inner case split per oracle: on `validStep sR.lastAction action`:
  * `false` — both sides return `pure none` with states unchanged; closed by
              `relTriple_pure_pure`.
  * `true`  — further split on `sR.lastAction` to identify the reachable
              predecessor action. Unreachable `(last, action)` pairs are
              discharged with `exfalso; simp [validStep]`. The remaining cases
              use `hybridRel_of_run_eq` or `hybridRel_of_run_evalDist_eq`
              (depending on whether the reduction samples a hidden scalar) to
              reduce the goal to an output + post-state equality under
              `hybridProj`, resolved by the reachability invariants
              `reachableInv_*` and the window helpers `hybridWindowInv_*`. -/
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
  -- sendA: at embedding epoch (challengedParty = .B), reduction samples fresh y while
  -- hybrid uses a; outputs (aG, xB·aG) agree, hybridProj absorbs the stA difference
  · rcases hrel with ⟨sent, rfl, hShape, hWin⟩
    cases hstep : validStep sR.lastAction .sendA
    · -- validStep = false: both return pure none
      have hstepH :
          validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .sendA
            = false := by
        simpa [hybridProj] using hstep
      have hrunL :
          ((reductionSendA (F := F) gp gen (a • gen)) ()).run sR = pure (none, sR) := by
        simp [reductionSendA, hstep, StateT.run_bind, StateT.run_get, pure_bind]
      have hrunH :
          ((hybridSendA (F := F) gp gen a) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent) =
            pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
        simp [hybridSendA, hstepH, StateT.run_bind, StateT.run_get, pure_bind]
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((reductionSendA (F := F) gp gen (a • gen) ()).run sR)
        ((hybridSendA (F := F) gp gen a ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR sent))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((none : Option (G × G)), sR))
          (b := ((none : Option (G × G)), hybridProj (F := F) (gen := gen) gp a b sR sent))
          ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
    · -- validStep = true: non-embedding vs embedding sub-cases.
      -- Closure roadmap (template = closed challA fire branch at `reductionChallA`).
      -- Step 1: split on `gp.challengedParty == .B && isOtherSendBeforeChall gp {sR with tA+1}`.
      -- Step 2 (non-embedding, branch `false`): both sides run `ddhCKA.send gen sR.stA`.
      --   Further case-split on `sR.stA`:
      --   · `.inr h`: both return `some (y·h, y·gen, .inl y)` for `y ← $F`; close via
      --     `hybridRel_of_run_eq` (F := F) (G := G) (gen := gen) with `sentPost := sent`
      --     and trivial `hrun_eq := rfl` after `simp [reductionSendA, hybridSendA, hstep,
      --     hcpB]` (non-embedding makes both oracles reduce to the shared `ddhCKA.send`).
      --   · `.inl _`: both return `pure none`; state unchanged; use `relTriple_pure_pure`.
      -- Step 3 (embedding, branch `true`): challengedParty = .B ∧ post-increment
      --   tA = tStar - 1 (the symmetric embedding point under the fixed
      --   `isOtherSendBeforeChall`).
      --   Reduction samples `y ← $F`, sets `stA := .inl y`; hybrid sets `stA := .inl a`.
      --   Outputs `(aG, xB·aG)` match literally (both sides use `xB := sR.stB`).
      --   Use `hybridRel_of_run_evalDist_eq` with `sentPost := true` (embedding sendA has
      --   occurred from B's perspective). The `evalDist_ext` absorbs the `y` sample against
      --   the deterministic `a` on the hybrid side via the identity rewrite of `stA` by
      --   `hybridProj` (the P=B `.inl` clause, whose `tA == gp.tStar` guard needs to be
      --   aligned with the symmetric embedding at `tStar - 1` before this proof goes
      --   through — see the `StateProjection` refactor plan above).
      --   Post-invariants: need a fresh helper `hybridWindowInv_reductionSendA_post` mirror
      --   of `hybridWindowInv_reductionChallB_post` at line 838.
      sorry
  -- recvA: both sides run oracleRecvA; hybridProj does not change stA at recvA-reachable
  -- states (stA = .inl y after a preceding sendA/challA), so recv sees the same stA
  · rcases hrel with ⟨sent, rfl, hInv, hWin⟩
    cases hstep : validStep sR.lastAction .recvA
    · have hstepH :
          validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .recvA
            = false := by
        simpa [hybridProj] using hstep
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((oracleRecvA (ddhCKA F G gen) ()).run sR)
        ((oracleRecvA (ddhCKA F G gen) ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR sent))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      have hrunL :
          ((oracleRecvA (ddhCKA F G gen) ()).run sR) = pure ((), sR) := by
        simp [oracleRecvA, hstep, StateT.run_bind, StateT.run_get, pure_bind]
      have hrunH :
          ((oracleRecvA (ddhCKA F G gen) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent)) =
            pure ((), hybridProj (F := F) (gen := gen) gp a b sR sent) := by
        simp [oracleRecvA, hstepH, StateT.run_bind, StateT.run_get, pure_bind]
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((), sR))
          (b := ((), hybridProj (F := F) (gen := gen) gp a b sR sent))
          ⟨rfl, ⟨sent, rfl, hInv, hWin⟩⟩)
    · cases hact : sR.lastAction with
      | none =>
          exfalso; simp [hact, validStep] at hstep
      | some act =>
          cases act with
          | sendA => exfalso; simp [hact, validStep] at hstep
          | recvA => exfalso; simp [hact, validStep] at hstep
          | recvB => exfalso; simp [hact, validStep] at hstep
          | challA => exfalso; simp [hact, validStep] at hstep
          -- validStep = true with lastAction = sendB/challB: recvA fires.
          -- Both sides read lastRhoB (same) and compute recv; hybrid's stA may
          -- differ (window rewrite), but `hybridProj` on the post-state restores
          -- the intended hybrid-side scalar, and the shape invariant is maintained
          -- (phaseShape uses projected stA = .inl b/a that matches lastRho).
          --
          -- Closure roadmap for `sendB` sub-case:
          --   Key observation: `oracleRecvA (ddhCKA F G gen)` is shared code. Invoke
          --   `hybridRel_of_run_eq` (F := F) (G := G) (gen := gen) with
          --     maR := (oracleRecvA (ddhCKA F G gen)) ()
          --     maH := (oracleRecvA (ddhCKA F G gen)) ()
          --     sentPost := if <embedding window> then true else sent.
          --   The `hrun_eq` goal requires showing that the `(output, hybridProj state')`
          --   projection of the reduction-side run equals the hybrid-side run. Case-split
          --   on `gp.challengedParty`:
          --   · `.A`: sendB preceding recvA occurs at embedding (tB = tStar - 1 post-
          --     increment after sendB). Use `reachableInv_sendB_or_challB` on `sH` (with
          --     `hShape := hInv`) to extract `∃ x y, sH.stA = .inl y ∧ sH.stB = .inl x`,
          --     etc. Since `sH.stA = (hybridProj sR).stA = sR.stA` here (stA not rewritten
          --     at lastAction = sendB for challenged A: requires tB = tStar + 1, false
          --     post-sendB), we have `sR.stA = .inl y` too. The key equality `keyA = y·aG`
          --     matches `lastKeyB = y·aG` giving `ok = true` on both sides. Post-`recvA`:
          --     `stA := .inr aG`, `stB` differs (sR has fresh y₂, sH has a), absorbed by
          --     hybridProj's stB rewrite at (lastAction = recvA, tB = tStar - 1).
          --   · `.B`: non-embedding recvA (since sendB at .B isn't the embedding). stA
          --     isn't rewritten (requires tA = tStar AND sent), so sR and sH match on stA,
          --     stB not rewritten (lastAction = sendB isn't in .B's stB rewrite list).
          --     Hence `sR = sH` entirely, and the proof is essentially
          --     `hybridRel_of_run_eq … hrun_eq := rfl`.
          --
          -- Closure roadmap for `challB` sub-case:
          --   At `lastAction = challB`, challengedParty MUST be .B (challB only fires when
          --   challengedParty = .B). Thus use `hybridShapeInv sH` third disjunct (direct-
          --   challB) to extract `sH.tA = tStar - 1, sH.tB = tStar, stA = .inl x, stB =
          --   .inl b, lastKeyB = some ((a*b)·gen), lastRhoB = some (b·gen)`. stA at
          --   challengedParty = .B with lastAction = challB requires `tA = tStar` for
          --   rewrite — but tA = tStar - 1, so NO rewrite. Hence sR.stA = sH.stA = .inl x.
          --   Both sides run oracleRecvA: `keyA = x·b·gen`; `ok = decide(x·b·gen =
          --   (a*b)·gen) ↔ x = a` — same on both sides (same x, same lastKeyB).
          --   Post-state: stA := .inr (b·gen), stB unchanged. hybridProj after recvA at
          --   .B rewrites stA if `(lastAction = recvA && tB = tStar)` — NOT in .B's stA
          --   rewrite list. Checks pass; close via `hybridRel_of_run_eq` with
          --   `sentPost := sent`.
          | sendB => sorry
          | challB => sorry
  -- sendB: symmetric to sendA. Embedding epoch is at challengedParty = .A with
  -- tB = tStar - 1; outputs (aG, xA·aG) agree, hybridProj absorbs the stB difference.
  · rcases hrel with ⟨sent, rfl, hShape, hWin⟩
    cases hstep : validStep sR.lastAction .sendB
    · have hstepH :
          validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .sendB
            = false := by
        simpa [hybridProj] using hstep
      have hrunL :
          ((reductionSendB (F := F) gp gen (a • gen)) ()).run sR = pure (none, sR) := by
        simp [reductionSendB, hstep, StateT.run_bind, StateT.run_get, pure_bind]
      have hrunH :
          ((hybridSendB (F := F) gp gen a) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent) =
            pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
        simp [hybridSendB, hstepH, StateT.run_bind, StateT.run_get, pure_bind]
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((reductionSendB (F := F) gp gen (a • gen) ()).run sR)
        ((hybridSendB (F := F) gp gen a ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR sent))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((none : Option (G × G)), sR))
          (b := ((none : Option (G × G)), hybridProj (F := F) (gen := gen) gp a b sR sent))
          ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
    · -- validStep = true: non-embedding vs embedding sub-cases.
      -- Symmetric to `sendA` (validStep = true) above with A/B swapped.
      -- Closure roadmap (template: A-version above + challB fire proof at `reductionChallB`).
      -- Step 1: split on `gp.challengedParty == .A && isOtherSendBeforeChall gp {sR with
      --   tB+1}`.
      -- Step 2 (non-embedding): both sides reduce to `ddhCKA.send gen sR.stB`.
      --   · `.inr h`: `hybridRel_of_run_eq` with `sentPost := sent`; trivial `hrun_eq`.
      --   · `.inl _`: `relTriple_pure_pure` with unchanged state.
      -- Step 3 (embedding, challengedParty = .A, tB = tStar - 1):
      --   Reduction samples `y ← $F`, sets `stB := .inl y`; hybrid sets `stB := .inl a`.
      --   Outputs `(aG, xA·aG)` match (both use `xA := sR.stA`). Close via
      --   `hybridRel_of_run_evalDist_eq` with `sentPost := true`; `hybridProj` absorbs
      --   `y → a` via the stB rewrite clause `challengedParty = .A ∧ tB = tStar - 1 ∧
      --   lastAction = sendB`. Post-invariant: add helper
      --   `hybridWindowInv_reductionSendB_post` mirror of `hybridWindowInv_reductionChallA_post`.
      sorry
  -- recvB: symmetric to recvA; hybridProj does not change stB at recvB-reachable states
  · rcases hrel with ⟨sent, rfl, hInv, hWin⟩
    cases hstep : validStep sR.lastAction .recvB
    · have hstepH :
          validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .recvB
            = false := by
        simpa [hybridProj] using hstep
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((oracleRecvB (ddhCKA F G gen) ()).run sR)
        ((oracleRecvB (ddhCKA F G gen) ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR sent))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      have hrunL :
          ((oracleRecvB (ddhCKA F G gen) ()).run sR) = pure ((), sR) := by
        simp [oracleRecvB, hstep, StateT.run_bind, StateT.run_get, pure_bind]
      have hrunH :
          ((oracleRecvB (ddhCKA F G gen) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent)) =
            pure ((), hybridProj (F := F) (gen := gen) gp a b sR sent) := by
        simp [oracleRecvB, hstepH, StateT.run_bind, StateT.run_get, pure_bind]
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((), sR))
          (b := ((), hybridProj (F := F) (gen := gen) gp a b sR sent))
          ⟨rfl, ⟨sent, rfl, hInv, hWin⟩⟩)
    · cases hact : sR.lastAction with
      | none =>
          exfalso; simp [hact, validStep] at hstep
      | some act =>
          cases act with
          | recvA => exfalso; simp [hact, validStep] at hstep
          | sendB => exfalso; simp [hact, validStep] at hstep
          | recvB => exfalso; simp [hact, validStep] at hstep
          | challB => exfalso; simp [hact, validStep] at hstep
          -- Symmetric to recvA: hybridProj's window rewrite on stB is absorbed
          -- by the post-state's own window projection; invariants maintained.
          --
          -- Closure roadmap for `sendA` sub-case (mirror of recvA/sendB case above):
          --   `oracleRecvB (ddhCKA F G gen)` is shared code. Invoke `hybridRel_of_run_eq`
          --   with maR = maH = oracleRecvB ().
          --   · challengedParty = .B: sendA is embedding (tA = tStar post-increment);
          --     use `reachableInv_sendA_or_challA` on `sH` to extract `∃ x y, stA = .inl y,
          --     stB = .inl x`, lastRhoA = y·gen, lastKeyA = y·x·gen. Post-recvB: stB :=
          --     .inr (y·gen) on both sides. stA differs (sR has fresh y₂ from sendA
          --     embedding, sH has a); absorbed by hybridProj's stA rewrite at
          --     (lastAction = recvB, stA clause for .B).
          --   · challengedParty = .A: non-embedding. stA/stB not rewritten at
          --     lastAction = sendA for .A (rewrite requires specific sentPre flag
          --     conditions absent here). Close with trivial `hrun_eq := rfl`.
          --
          -- Closure roadmap for `challA` sub-case:
          --   At `lastAction = challA`, challengedParty MUST be .A. Use `hybridShapeInv sH`
          --   second disjunct (direct-challA) to extract: `sH.tA = tStar, sH.tB = tStar - 1,
          --   stA = .inl b, stB = .inl x, lastKeyA = some ((a*b)·gen), lastRhoA = some
          --   (b·gen)`. stA at `.A` with lastAction = challA requires `tA = tStar` for
          --   rewrite, so YES rewrite: sR.stA = .inl z (fresh), sH.stA = .inl b. stB at
          --   .A with lastAction = challA: rewrite requires `sent && challA`, so if
          --   `sent = true`, stB is rewritten to .inl a.
          --   Both sides run oracleRecvB which reads stB: the F-scalar values differ
          --   (sR: some z₂ vs sH: a), so `keyB := x·ρ where x := stB`. But wait —
          --   recvB reads stB, not stA. The stB match/mismatch matters. In this trace,
          --   for `lastAction = challA`, there HAS been a prior sendA (in the case
          --   `sent = true`), whose embedding at .B doesn't fire (we're at .A). So stB
          --   from the `.A + challA` shape invariant: stB = .inl x where x = x₀ initially
          --   or some prior recv value. The hybridProj does NOT rewrite stB at
          --   lastAction = challA for .A unless `sent = true` specifically. Use the
          --   window invariant + sendA prior trace to establish ok_R = ok_H, then close
          --   via `hybridRel_of_run_eq` (sentPost := sent). The trickiest part is the
          --   sentPost choice; likely `sentPost := true` to set up the next step's
          --   projection correctly.
          | sendA => sorry
          | challA => sorry
  -- challA: reduction uses (gB, gT) with stA := z; hybrid uses (b·G, ab·G) with stA := b;
  -- outputs agree since gB = b·gen and gT = (a*b)·gen; hybridWindowInv tracks the window
  · rcases hrel with ⟨sent, rfl, hShape, hWin⟩
    -- The oracle only fires when challengedParty = .A ∧ validStep ∧ isChallengeEpoch.
    -- Otherwise returns pure none on both sides with hybridProj's output agreeing.
    by_cases hcpA : gp.challengedParty = .A
    · by_cases hvs : validStep sR.lastAction .challA = true
      · by_cases hchal : isChallengeEpoch gp { sR with tA := sR.tA + 1 } = true
        · -- Fires: reduction samples z, hybrid uses b. Outputs agree (both (bG, abG)).
          -- Post-states coincide under hybridProj (challA window rewrites stA := .inl b).
          have htA : sR.tA + 1 = gp.tStar := by
            simpa [isChallengeEpoch, hcpA] using hchal
          have hvsH : validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .challA
              = true := by
            simpa [hybridProj] using hvs
          have hchalH : isChallengeEpoch gp
              { hybridProj (F := F) (gen := gen) gp a b sR sent with
                tA := (hybridProj (F := F) (gen := gen) gp a b sR sent).tA + 1 } = true := by
            simpa [isChallengeEpoch, hybridProj] using hchal
          have hReach :
              reachableShape gen (hybridProj (F := F) (gen := gen) gp a b sR sent) := by
            cases hShape with
            | inl hReach => exact hReach
            | inr hRest =>
                cases hRest with
                | inl hDirectA =>
                    exfalso
                    simpa [hDirectA.2.1, validStep] using hvsH
                | inr hDirectB =>
                    exfalso
                    simpa [hDirectB.2.1, validStep] using hvsH
          cases hact : sR.lastAction with
          | none =>
              have hactH :
                  (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction = none := by
                simpa [hybridProj] using hact
              rcases reachableShape_none_or_recvA
                  (F := F) (G := G) (gen := gen)
                  (hybridProj (F := F) (gen := gen) gp a b sR sent) hReach (Or.inl hactH) with
                ⟨x, hstApre, hstBpre, hrApre, hrBpre, hkApre, hkBpre⟩
              have htB : sR.tB = gp.tStar - 1 := by
                rcases hReach with ⟨hCtr, _⟩
                have htEqH :
                    (hybridProj (F := F) (gen := gen) gp a b sR sent).tA =
                      (hybridProj (F := F) (gen := gen) gp a b sR sent).tB := by
                  simpa [phaseCounterInv, hactH] using hCtr
                have htEq : sR.tA = sR.tB := by
                  simpa [hybridProj] using htEqH
                omega
              have hrunR :
                  ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR =
                    (($ᵗ F : ProbComp F) >>= fun z =>
                      pure
                        ((some ((b • gen), ((a * b) • gen)) : Option (G × G)),
                          { sR with
                            tA := sR.tA + 1
                            stA := (.inl z : F ⊕ G)
                            lastRhoA := some (b • gen)
                            lastKeyA := some ((a * b) • gen)
                            lastAction := some .challA })) := by
                simp [reductionChallA, hcpA, hvs, hchal, StateT.run_bind, StateT.run_get,
                  pure_bind, StateT.run_pure]
              have hrunH :
                  ((hybridChallA (F := F) gp gen a b) ()).run
                    (hybridProj (F := F) (gen := gen) gp a b sR sent) =
                    pure
                      ((some ((b • gen), ((a * b) • gen)) : Option (G × G)),
                        { hybridProj (F := F) (gen := gen) gp a b sR sent with
                          tA := (hybridProj (F := F) (gen := gen) gp a b sR sent).tA + 1
                          stA := (.inl b : F ⊕ G)
                          lastRhoA := some (b • gen)
                          lastKeyA := some ((a * b) • gen)
                          lastAction := some .challA }) := by
                simp [hybridChallA, hcpA, hvsH, hchalH, StateT.run_bind, StateT.run_get,
                  pure_bind, StateT.run_pure]
              refine hybridRel_of_run_evalDist_eq
                (F := F) (G := G) (gen := gen)
                (maR := (reductionChallA (F := F) gp (b • gen) ((a * b) • gen)) ())
                (maH := (hybridChallA (F := F) gp gen a b) ())
                (sR := sR) (gp := gp) (a := a) (b := b) (sentPre := sent) (sentPost := false)
                ?_ ?_ ?_
              · rw [hrunR, hrunH]
                apply evalDist_ext
                intro q
                simp [hybridProj, hcpA, hact, htA]
              · intro p hp
                rw [hrunR] at hp
                simp at hp
                rcases hp with ⟨z, _, rfl⟩
                refine Or.inr (Or.inl ?_)
                refine ⟨hcpA, rfl, ?_, ?_, x, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simp [hybridProj, htA]
                · exact htB
                · simp [hybridProj, hcpA, htA]
                · simpa [hybridProj, hcpA, hact] using hstBpre
                · simp [hybridProj]
                · simpa [hybridProj, hcpA, hact] using hrBpre
                · simp [hybridProj]
                · simpa [hybridProj, hcpA, hact] using hkBpre
              · intro p hp
                rw [hrunR] at hp
                simp at hp
                rcases hp with ⟨z, _, rfl⟩
                exact hybridWindowInv_reductionChallA_post
                  (F := F) (G := G) (gen := gen) gp a b z sR hcpA
          | some act =>
              cases act with
              | sendA => exfalso; simp [hact, validStep] at hvs
              | recvA =>
                  have hactH :
                      (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction =
                        some .recvA := by
                    simpa [hybridProj] using hact
                  rcases reachableShape_none_or_recvA
                      (F := F) (G := G) (gen := gen)
                      (hybridProj (F := F) (gen := gen) gp a b sR sent) hReach (Or.inr hactH) with
                    ⟨x, hstApre, hstBpre, hrApre, hrBpre, hkApre, hkBpre⟩
                  have htB : sR.tB = gp.tStar - 1 := by
                    rcases hReach with ⟨hCtr, _⟩
                    have htEqH :
                        (hybridProj (F := F) (gen := gen) gp a b sR sent).tA =
                          (hybridProj (F := F) (gen := gen) gp a b sR sent).tB := by
                      simpa [phaseCounterInv, hactH] using hCtr
                    have htEq : sR.tA = sR.tB := by
                      simpa [hybridProj] using htEqH
                    omega
                  have hneqB : gp.tStar - 1 ≠ gp.tStar := by
                    omega
                  have hsB : ∃ w : F, sR.stB = (.inl w : F ⊕ G) := by
                    cases hsb : sR.stB with
                    | inl w =>
                        exact ⟨w, rfl⟩
                    | inr g =>
                        simp [hybridProj, hcpA, hact, htB, hsb] at hstBpre
                  have hrunR :
                      ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR =
                        (($ᵗ F : ProbComp F) >>= fun z =>
                          pure
                            ((some ((b • gen), ((a * b) • gen)) : Option (G × G)),
                              { sR with
                                tA := sR.tA + 1
                                stA := (.inl z : F ⊕ G)
                                lastRhoA := some (b • gen)
                                lastKeyA := some ((a * b) • gen)
                                lastAction := some .challA })) := by
                    simp [reductionChallA, hcpA, hvs, hchal, StateT.run_bind, StateT.run_get,
                      pure_bind, StateT.run_pure]
                  have hrunH :
                      ((hybridChallA (F := F) gp gen a b) ()).run
                        (hybridProj (F := F) (gen := gen) gp a b sR sent) =
                        pure
                          ((some ((b • gen), ((a * b) • gen)) : Option (G × G)),
                            { hybridProj (F := F) (gen := gen) gp a b sR sent with
                              tA := (hybridProj (F := F) (gen := gen) gp a b sR sent).tA + 1
                              stA := (.inl b : F ⊕ G)
                              lastRhoA := some (b • gen)
                              lastKeyA := some ((a * b) • gen)
                              lastAction := some .challA }) := by
                    simp [hybridChallA, hcpA, hvsH, hchalH, StateT.run_bind, StateT.run_get,
                      pure_bind, StateT.run_pure]
                  refine hybridRel_of_run_evalDist_eq
                    (F := F) (G := G) (gen := gen)
                    (maR := (reductionChallA (F := F) gp (b • gen) ((a * b) • gen)) ())
                    (maH := (hybridChallA (F := F) gp gen a b) ())
                    (sR := sR) (gp := gp) (a := a) (b := b) (sentPre := sent) (sentPost := true)
                    ?_ ?_ ?_
                  · rw [hrunR, hrunH]
                    apply evalDist_ext
                    intro q
                    simp [hybridProj, hcpA, hact, htA, htB, hneqB]
                  · intro p hp
                    rw [hrunR] at hp
                    simp at hp
                    rcases hp with ⟨z, _, rfl⟩
                    refine Or.inl ?_
                    refine ⟨?_, ?_⟩
                    · have hphase : gp.tStar = gp.tStar - 1 + 1 := by
                        omega
                      simpa [phaseCounterInv, hybridProj, htA, htB] using hphase
                    · refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
                      · simp [hybridProj, hcpA, htA, htB]
                      · rcases hsB with ⟨w, hsb⟩
                        simp [hybridProj, hcpA, htA, htB, hsb]
                      · simp [hybridProj]
                      · simpa [hybridProj, hcpA, hact] using hrBpre
                      · simpa [hybridProj, smul_smul, mul_comm, mul_left_comm, mul_assoc]
                      · simpa [hybridProj, hcpA, hact] using hkBpre
                  · intro p hp
                    rw [hrunR] at hp
                    simp at hp
                    rcases hp with ⟨z, _, rfl⟩
                    exact hybridWindowInv_reductionChallA_post
                      (F := F) (G := G) (gen := gen) gp a b z sR hcpA
              | recvB => exfalso; simp [hact, validStep] at hvs
              | sendB => exfalso; simp [hact, validStep] at hvs
              | challA => exfalso; simp [hact, validStep] at hvs
              | challB => exfalso; simp [hact, validStep] at hvs
        · -- validStep ok, not in challenge epoch: returns pure none
          have hvsH : validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .challA
              = true := by simpa [hybridProj] using hvs
          have hchalH : isChallengeEpoch gp
              { hybridProj (F := F) (gen := gen) gp a b sR sent with
                tA := (hybridProj (F := F) (gen := gen) gp a b sR sent).tA + 1 } = false := by
            have : isChallengeEpoch gp { sR with tA := sR.tA + 1 } = false := by
              cases h : isChallengeEpoch gp { sR with tA := sR.tA + 1 }
              · rfl
              · exact absurd h hchal
            simpa [isChallengeEpoch, hybridProj] using this
          have hrunL :
              ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR
                = pure (none, sR) := by
            simp [reductionChallA, hcpA, hvs, hchal, StateT.run_bind, StateT.run_get,
              pure_bind, StateT.run_pure]
          have hrunH :
              ((hybridChallA (F := F) gp gen a b) ()).run
                (hybridProj (F := F) (gen := gen) gp a b sR sent)
                = pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
            have hcpAH : (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction
                = sR.lastAction := by simp [hybridProj]
            simp [hybridChallA, hcpA, hvsH, hchalH, StateT.run_bind, StateT.run_get,
              pure_bind, StateT.run_pure]
          change OracleComp.ProgramLogic.Relational.RelTriple
            ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen) ()).run sR)
            ((hybridChallA (F := F) gp gen a b ()).run
              (hybridProj (F := F) (gen := gen) gp a b sR sent))
            (fun pR pH =>
              pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          rw [hrunL, hrunH]
          exact
            (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
              (spec₁ := unifSpec) (spec₂ := unifSpec)
              (R := fun pR pH =>
                pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
              (a := ((none : Option (G × G)), sR))
              (b := ((none : Option (G × G)),
                hybridProj (F := F) (gen := gen) gp a b sR sent))
              ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
      · -- validStep false: returns pure none
        have hvs' : validStep sR.lastAction .challA = false := by
          cases h : validStep sR.lastAction .challA
          · rfl
          · exact absurd h hvs
        have hvsH : validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .challA
            = false := by simpa [hybridProj] using hvs'
        have hrunL :
            ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR
              = pure (none, sR) := by
          simp [reductionChallA, hcpA, hvs', StateT.run_pure]
        have hrunH :
            ((hybridChallA (F := F) gp gen a b) ()).run
              (hybridProj (F := F) (gen := gen) gp a b sR sent)
              = pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
          simp [hybridChallA, hcpA, hvsH, StateT.run_pure]
        change OracleComp.ProgramLogic.Relational.RelTriple
          ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen) ()).run sR)
          ((hybridChallA (F := F) gp gen a b ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent))
          (fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        rw [hrunL, hrunH]
        exact
          (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
            (spec₁ := unifSpec) (spec₂ := unifSpec)
            (R := fun pR pH =>
              pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
            (a := ((none : Option (G × G)), sR))
            (b := ((none : Option (G × G)),
              hybridProj (F := F) (gen := gen) gp a b sR sent))
            ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
    · -- challengedParty ≠ .A: returns pure none on both sides
      have hrunL :
          ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR
            = pure (none, sR) := by
        simp [reductionChallA, hcpA, StateT.run_pure]
      have hrunH :
          ((hybridChallA (F := F) gp gen a b) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent)
            = pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
        simp [hybridChallA, hcpA, StateT.run_pure]
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((reductionChallA (F := F) gp (b • gen) ((a * b) • gen) ()).run sR)
        ((hybridChallA (F := F) gp gen a b ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR sent))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((none : Option (G × G)), sR))
          (b := ((none : Option (G × G)),
            hybridProj (F := F) (gen := gen) gp a b sR sent))
          ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
  -- challB: symmetric to challA for the challenged-B case
  · rcases hrel with ⟨sent, rfl, hShape, hWin⟩
    by_cases hcpB : gp.challengedParty = .B
    · by_cases hvs : validStep sR.lastAction .challB = true
      · by_cases hchal : isChallengeEpoch gp { sR with tB := sR.tB + 1 } = true
        · have htB : sR.tB + 1 = gp.tStar := by
            simpa [isChallengeEpoch, hcpB] using hchal
          have hvsH : validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .challB
              = true := by
            simpa [hybridProj] using hvs
          have hchalH : isChallengeEpoch gp
              { hybridProj (F := F) (gen := gen) gp a b sR sent with
                tB := (hybridProj (F := F) (gen := gen) gp a b sR sent).tB + 1 } = true := by
            simpa [isChallengeEpoch, hybridProj] using hchal
          have hReach :
              reachableShape gen (hybridProj (F := F) (gen := gen) gp a b sR sent) := by
            cases hShape with
            | inl hReach => exact hReach
            | inr hRest =>
                cases hRest with
                | inl hA =>
                    exfalso
                    simpa [hcpB] using hA.1
                | inr hB =>
                    exfalso
                    simpa [hB.2.1, validStep] using hvsH
          cases hact : sR.lastAction with
          | none => exfalso; simp [hact, validStep] at hvs
          | some act =>
              cases act with
              | sendA => exfalso; simp [hact, validStep] at hvs
              | recvA => exfalso; simp [hact, validStep] at hvs
              | sendB => exfalso; simp [hact, validStep] at hvs
              | challA => exfalso; simp [hact, validStep] at hvs
              | challB => exfalso; simp [hact, validStep] at hvs
              | recvB =>
                  have hactH :
                      (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction =
                        some .recvB := by
                    simpa [hybridProj] using hact
                  rcases reachableShape_recvB
                      (F := F) (G := G) (gen := gen)
                      (hybridProj (F := F) (gen := gen) gp a b sR sent) hReach hactH with
                    ⟨x, hstApre, hstBpre, hrApre, hrBpre, hkApre, hkBpre⟩
                  have htA : sR.tA = gp.tStar - 1 := by
                    rcases hReach with ⟨hCtr, _⟩
                    have htEqH :
                        (hybridProj (F := F) (gen := gen) gp a b sR sent).tA =
                          (hybridProj (F := F) (gen := gen) gp a b sR sent).tB := by
                      simpa [phaseCounterInv, hactH] using hCtr
                    have htEq : sR.tA = sR.tB := by
                      simpa [hybridProj] using htEqH
                    omega
                  have hneqA : gp.tStar - 1 ≠ gp.tStar := by
                    omega
                  have hrunR :
                      ((reductionChallB (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR =
                        (($ᵗ F : ProbComp F) >>= fun z =>
                          pure
                            ((some ((b • gen), ((a * b) • gen)) : Option (G × G)),
                              { sR with
                                tB := sR.tB + 1
                                stB := (.inl z : F ⊕ G)
                                lastRhoB := some (b • gen)
                                lastKeyB := some ((a * b) • gen)
                                lastAction := some .challB })) := by
                    simp [reductionChallB, hcpB, hvs, hchal, StateT.run_bind, StateT.run_get,
                      pure_bind]
                  have hrunH :
                      ((hybridChallB (F := F) gp gen a b) ()).run
                        (hybridProj (F := F) (gen := gen) gp a b sR sent) =
                        pure
                          ((some ((b • gen), ((a * b) • gen)) : Option (G × G)),
                            { hybridProj (F := F) (gen := gen) gp a b sR sent with
                              tB := (hybridProj (F := F) (gen := gen) gp a b sR sent).tB + 1
                              stB := (.inl b : F ⊕ G)
                              lastRhoB := some (b • gen)
                              lastKeyB := some ((a * b) • gen)
                              lastAction := some .challB }) := by
                    simp [hybridChallB, hcpB, hvsH, hchalH, StateT.run_bind, StateT.run_get,
                      pure_bind]
                  refine hybridRel_of_run_evalDist_eq
                    (F := F) (G := G) (gen := gen)
                    (maR := (reductionChallB (F := F) gp (b • gen) ((a * b) • gen)) ())
                    (maH := (hybridChallB (F := F) gp gen a b) ())
                    (sR := sR) (gp := gp) (a := a) (b := b) (sentPre := sent) (sentPost := sent)
                    ?_ ?_ ?_
                  · rw [hrunR, hrunH]
                    apply evalDist_ext
                    intro q
                    simp [hybridProj, hcpB, hact, htA, htB, hneqA]
                  · intro p hp
                    rw [hrunR] at hp
                    simp at hp
                    rcases hp with ⟨z, _, rfl⟩
                    refine Or.inr (Or.inr ?_)
                    refine ⟨hcpB, rfl, htA, ?_, x, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · simp [hybridProj, htB]
                    · simpa [hybridProj, hcpB, hact, htA, hneqA] using hstApre
                    · simp [hybridProj, hcpB, htA, htB]
                    · simpa [hybridProj, hcpB, hact] using hrApre
                    · simp [hybridProj]
                    · simpa [hybridProj, hcpB, hact, htA] using hkApre
                    · simp [hybridProj]
                  · intro p hp
                    rw [hrunR] at hp
                    simp at hp
                    rcases hp with ⟨z, _, rfl⟩
                    exact hybridWindowInv_reductionChallB_post
                      (F := F) (G := G) (gen := gen) gp a b z sR hcpB
        · have hvsH : validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .challB
              = true := by simpa [hybridProj] using hvs
          have hchalH : isChallengeEpoch gp
              { hybridProj (F := F) (gen := gen) gp a b sR sent with
                tB := (hybridProj (F := F) (gen := gen) gp a b sR sent).tB + 1 } = false := by
            have : isChallengeEpoch gp { sR with tB := sR.tB + 1 } = false := by
              cases h : isChallengeEpoch gp { sR with tB := sR.tB + 1 }
              · rfl
              · exact absurd h hchal
            simpa [isChallengeEpoch, hybridProj] using this
          have hrunL :
              ((reductionChallB (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR
                = pure (none, sR) := by
            simp [reductionChallB, hcpB, hvs, hchal, StateT.run_pure]
          have hrunH :
              ((hybridChallB (F := F) gp gen a b) ()).run
                (hybridProj (F := F) (gen := gen) gp a b sR sent)
                = pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
            simp [hybridChallB, hcpB, hvsH, hchalH, StateT.run_pure]
          change OracleComp.ProgramLogic.Relational.RelTriple
            ((reductionChallB (F := F) gp (b • gen) ((a * b) • gen) ()).run sR)
            ((hybridChallB (F := F) gp gen a b ()).run
              (hybridProj (F := F) (gen := gen) gp a b sR sent))
            (fun pR pH =>
              pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          rw [hrunL, hrunH]
          exact
            (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
              (spec₁ := unifSpec) (spec₂ := unifSpec)
              (R := fun pR pH =>
                pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
              (a := ((none : Option (G × G)), sR))
              (b := ((none : Option (G × G)),
                hybridProj (F := F) (gen := gen) gp a b sR sent))
              ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
      · have hvs' : validStep sR.lastAction .challB = false := by
          cases h : validStep sR.lastAction .challB
          · rfl
          · exact absurd h hvs
        have hvsH : validStep (hybridProj (F := F) (gen := gen) gp a b sR sent).lastAction .challB
            = false := by simpa [hybridProj] using hvs'
        have hrunL :
            ((reductionChallB (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR
              = pure (none, sR) := by
          simp [reductionChallB, hcpB, hvs', StateT.run_pure]
        have hrunH :
            ((hybridChallB (F := F) gp gen a b) ()).run
              (hybridProj (F := F) (gen := gen) gp a b sR sent)
              = pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
          simp [hybridChallB, hcpB, hvsH, StateT.run_pure]
        change OracleComp.ProgramLogic.Relational.RelTriple
          ((reductionChallB (F := F) gp (b • gen) ((a * b) • gen) ()).run sR)
          ((hybridChallB (F := F) gp gen a b ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent))
          (fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
        rw [hrunL, hrunH]
        exact
          (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
            (spec₁ := unifSpec) (spec₂ := unifSpec)
            (R := fun pR pH =>
              pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
            (a := ((none : Option (G × G)), sR))
            (b := ((none : Option (G × G)),
              hybridProj (F := F) (gen := gen) gp a b sR sent))
            ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
    · have hrunL :
          ((reductionChallB (F := F) gp (b • gen) ((a * b) • gen)) ()).run sR
            = pure (none, sR) := by
        simp [reductionChallB, hcpB, StateT.run_pure]
      have hrunH :
          ((hybridChallB (F := F) gp gen a b) ()).run
            (hybridProj (F := F) (gen := gen) gp a b sR sent)
            = pure (none, hybridProj (F := F) (gen := gen) gp a b sR sent) := by
        simp [hybridChallB, hcpB, StateT.run_pure]
      change OracleComp.ProgramLogic.Relational.RelTriple
        ((reductionChallB (F := F) gp (b • gen) ((a * b) • gen) ()).run sR)
        ((hybridChallB (F := F) gp gen a b ()).run
          (hybridProj (F := F) (gen := gen) gp a b sR sent))
        (fun pR pH =>
          pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
      rw [hrunL, hrunH]
      exact
        (OracleComp.ProgramLogic.Relational.relTriple_pure_pure
          (spec₁ := unifSpec) (spec₂ := unifSpec)
          (R := fun pR pH =>
            pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2)
          (a := ((none : Option (G × G)), sR))
          (b := ((none : Option (G × G)),
            hybridProj (F := F) (gen := gen) gp a b sR sent))
          ⟨rfl, ⟨sent, rfl, hShape, hWin⟩⟩)
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
steps to absorb `a` into the honest oracle's `y ← $F` and `b` into `x ← $F`.

Closure roadmap. Since the hybrid's `a, b` appear at fixed positions (the embedding
sendA/sendB/challA/challB for each challengedParty), this is a two-step absorption:
  Step A (commute `a` past simulateQ): the external `a ← $F` is used exactly once
    inside the specific embedding-send oracle (sendA at .B or sendB at .A). Use a
    relational argument with `runHybrid_a_then_step ≡ step_then_runHybrid_a`
    commuting via `probOutput_bind_bind_swap` on the surrounding binds.
  Step B (absorb `a` into honest's fresh `y`): at the embedding step, the hybrid
    hard-codes `stA/stB := .inl a`; the honest `ddhCKA.send` samples `y ← $F` and
    sets `stA/stB := .inl y`. Use `probOutput_bind_bijective_uniform_cross` with
    the identity bijection `id : F → F` to identify the two uniform samples.
  Symmetric steps for `b` at challA/challB.
Easier alternative: define an intermediate `semiHybridGame` where `a` is absorbed
but `b` is still external, then chain two absorptions. Each absorption is a ~50-line
proof that mirrors the structure of `Examples/ElGamal/Basic.lean` lines 195-280. -/
private lemma securityReduction_hybrid_to_honest (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityHybridGame (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitFalseGame (gen := gen) gp adversary] := by
  sorry

/-- **Real-branch lemma.**
`Pr[ℬ = true | DDH_real] = Pr[𝒜 = false | CKA^{b = false}]`.

Chains the four real-branch steps:
`(1) probOutput_ddhExpReal_securityReduction`,
`(2) securityReduction_real_to_hybrid`,
`(3) securityReduction_hybrid_to_honest`,
`(4) probOutput_securityExpFixedBit_false`. -/
lemma securityReduction_real (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  rw [probOutput_ddhExpReal_securityReduction, probOutput_securityExpFixedBit_false,
      securityReduction_real_to_hybrid (gen := gen) gp hΔ adversary]
  exact securityReduction_hybrid_to_honest (gen := gen) gp hΔ adversary

/-- **Random-branch lemma.**
`Pr[ℬ = true | DDH_rand] = Pr[𝒜 = false | CKA^{b = true}]`.

Bijectivity of `(·) • gen : F → G` (hypothesis `hg`) couples `c • gen` with
`$ᵗ G`, matching the honest challenge `(x • gen, $ᵗ G)` at `b = true`.

Closure roadmap: this is NOT a single bijective absorption — the reduction's
`reductionChallA/B` and `reductionSendA/B` differ from the honest `oracleChallA/B`
and the shared `ddhCKA.send` in their hidden-state updates. The right structure is
the same relational argument used in the real branch, but with a simpler projection:

  1. Introduce `securityReductionRandGame` (mirror of `securityReductionRealGame`) —
     a one-shot `ProbComp Bool` wrapping `simulateQ reductionOracleImpl` with
     `gT := c • gen` for independent `c ← $F`.
  2. Prove `Pr[ℬ = true | ddhExpRand ...] = Pr[= false | securityReductionRandGame ...]`
     via `probOutput_not_map` (mirror of `probOutput_ddhExpReal_securityReduction`).
  3. Prove `Pr[= false | securityReductionRandGame ...] = Pr[= false |
     securityExpFixedBit (ddhCKA F G gen) adversary true gp]` via a fresh
     `randRel : GameState → GameState → Prop` (simpler than `hybridRel`: the
     divergence is only at the challA/challB step and in the subsequent `.inl z`
     reduction-state vs `.inl y` honest-state, which is unobservable since
     `corruptA/B` is blocked in the challenge window and the very next `recvA/B`
     overwrites both to `.inr ρ`).
  4. The key sample-absorbing step: at challA, `reductionChallA` samples `z ← $F`
     (state) with outputs `(bG, cG)`; the honest `oracleChallA` at b=true samples
     `y ← $F` (inside `ddhCKA.send`) and `outKey ← $ᵗ G`, outputting `(yG, outKey)`.
     Coupling:
       `y ↔ b` (uniform `F` ↔ uniform `F` via identity)
       `outKey ↔ cG` (uniform `G` ↔ uniform `F` via bijection `(·) • gen`)
       reduction's `z` absorbs into honest's internal state scalar.
     Formally: `probOutput_bind_bijective_uniform_cross hg` handles `outKey ↔ cG`;
     the other two are `probOutput_bind_bind_swap` to commute the external `b, c`
     past `simulateQ` plus a relational argument for `y ↔ b` and `z` absorption.

Alternative (simpler) approach: define `randRel` + `randProj` inline, then reuse
the existing `relTriple_simulateQ_run'` scaffolding verbatim. The `randProj` would
rewrite `stA/stB` only at (challengedParty, lastAction) = (.A, challA) and (.B, challB)
to absorb the `z` scalar into the value implied by the outer `b`. -/
lemma securityReduction_rand (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpRand gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary true gp] := by
  sorry

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
    (gp : GameParams) (adversary : SecurityAdversary (F ⊕ G) G G) : ℝ :=
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
    (adversary : SecurityAdversary (F ⊕ G) G G) :
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
the challenge bit. Under bijectivity of `· • gen`, the challenge oracle output
`outKey` is distributionally independent of `state.b`, so the two fixed-bit games
induce identical failure events.

Closure roadmap. The two fixed-bit games differ ONLY inside `oracleChallA/B`, where
the `b = true` branch samples `outKey ← $ᵗ I` and the `b = false` branch returns
`outKey := key := y · h` deterministically. The `⊥` (failure) event is
`probFailure mx = 1 - (Pr[= true | mx] + Pr[= false | mx])`. Since `⊥` is determined
by the underlying `ProbComp`'s failure paths (`empty <$F>` or aborts), and neither
branch of the challA/challB output is a failure path, the key insight is: both
`outKey ← $ᵗ G` (at `b = true`) and `pure key` (at `b = false`) are *non-failing*
operations. Hence the failure probability is independent of `b`.

Formally:
  1. Introduce `securityExpFixedBit_noChallOutput` — a variant that strips the
     `outKey` step from both challenge oracles (just returns `some (ρ, 0)`).
  2. Show by oracle-level rewrite (commute with `probFailure`) that
     `Pr[⊥ | securityExpFixedBit ... b gp] = Pr[⊥ | securityExpFixedBit_noChallOutput ...]`
     for every `b ∈ {true, false}`. Uses `probFailure_bind_eq_tsum` and the fact
     that for any non-failing `mx : ProbComp α`, `Pr[⊥ | mx >>= f] = Pr[⊥ | f]`
     integrated over `mx`'s support.
  3. Conclude equality of both sides.

Alternative: a direct relational argument `probFailure_eq_of_noFailureDistOracle`
if such a lemma exists — search `ToMathlib/ProbabilityTheory/Coupling.lean` and
`VCVio/OracleComp/QueryTracking/`. -/
private lemma probFailure_securityExpFixedBit_eq
    (gp : GameParams) (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary true gp] =
    Pr[⊥ | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  sorry

/-- **DDH-CKA security (per-adversary form)** [ACD19, Theorem 3].

For any CKA adversary `𝒜`, the CKA advantage is bounded by the DDH
guess-advantage of the reduction `ℬ = securityReduction gp 𝒜`:

  `securityAdvantage(ddhCKA, 𝒜, gp) ≤ ddhGuessAdvantage(gen, ℬ)`

Derived from `security_le_ddh_plus_failGap` by collapsing the failure gap
using `probFailure_securityExpFixedBit_eq`. -/
theorem security (gp : GameParams)
    (hΔ : gp.deltaCKA = 1)
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) :
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

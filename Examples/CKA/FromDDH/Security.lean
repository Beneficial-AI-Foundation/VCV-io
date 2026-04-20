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

/-! ### Hybrid coupling: projection, invariant, oracle-step lemma

`reductionOracleImpl` and `hybridOracleImpl` agree on every
transcript-visible field but store different hidden scalars (`stA`, `stB :
F ⊕ G`) in a narrow **challenge window** around `gp.tStar`:

| Epoch                               | Reduction      | Hybrid           |
|-------------------------------------|----------------|------------------|
| `tA = t* - 1`, `lastAction = sendA` | `.inl y` fresh | `.inl a` DDH exp |
| `tB = t* - 1`, `lastAction = sendB` | `.inl y` fresh | `.inl a` DDH exp |
| `tA = t*`,     `lastAction = challA`| `.inl z` fresh | `.inl b` DDH exp |
| `tB = t*`,     `lastAction = challB`| `.inl z` fresh | `.inl b` DDH exp |

`hybridProj` rewrites the hidden scalar to the DDH scalar inside the
window and is the identity outside; `hybridRel gp a b sR sH := sH =
hybridProj gp a b sR`.

The oracle-step lemma `hybridRel_query` splits into three phases:

- **identity**: outside the window (or shared code inside) both oracles
  run the same code on the same state;
- **embedding**: one `sendA`/`sendB` step absorbs `y ← $F` into `a` by
  identity-bijection coupling;
- **challenge**: the symmetric `challA`/`challB` step absorbs `z` into `b`.

Corruption is gated out of the window by `gp.deltaCKA = 1`. -/

/-- Challenge window: some party's counter is in `{t* - 1, t*}`. Outside,
`hybridProj gp a b s = s`. -/
private def inChallWindow (gp : GameParams) (s : GameState (F ⊕ G) G G) : Bool :=
  (s.tA == gp.tStar - 1) || (s.tA == gp.tStar) ||
    (s.tB == gp.tStar - 1) || (s.tB == gp.tStar)

/-- State-derived "pre-challenge embedding has fired" bit, monotone in
`(s.tA, s.tB)` (see `inferSent_mono`). -/
private def inferSent (gp : GameParams) (s : GameState (F ⊕ G) G G) : Bool :=
  match gp.challengedParty with
  | .A => decide (Odd gp.tStar ∧ gp.tStar ≥ 3 ∧ s.tB ≥ gp.tStar - 1)
  | .B => decide (Even gp.tStar ∧ gp.tStar ≥ 2 ∧ s.tA ≥ gp.tStar - 1)

/-- In-window rewrite: `.inl y` / `.inl z` on the reduction side ↦ `.inl a`
/ `.inl b` on the hybrid side (see the per-epoch table in the section
header). -/
private noncomputable def windowRewrite (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) : GameState (F ⊕ G) G G :=
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
          if (s.lastAction = some .sendA && s.tA == gp.tStar - 1) ||
              (s.lastAction = some .recvB && s.tA == gp.tStar - 1 &&
                s.tB == gp.tStar - 1) ||
              (s.lastAction = some .sendB && s.tA == gp.tStar - 1 &&
                s.tB == gp.tStar) ||
              (s.lastAction = some .challB && s.tA == gp.tStar - 1 &&
                s.tB == gp.tStar)
          then (.inl a : F ⊕ G)
          else s.stA
      | _, .inr _ => s.stA
    stB := match gp.challengedParty, s.stB with
      | .A, .inl _ =>
          if s.tB == gp.tStar - 1 &&
              (s.lastAction = some .sendB ||
               s.lastAction = some .recvA ||
               (inferSent gp s && (s.lastAction = some .sendA ||
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

/-- Coupling projection `π : GameState → GameState`: identity outside the
window, `windowRewrite` inside. -/
private noncomputable def hybridProj (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) : GameState (F ⊕ G) G G :=
  if inChallWindow gp s then windowRewrite (F := F) (gen := gen) gp a b s
  else s

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
     [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] in
/-- `inferSent` is monotone in `(s.tA, s.tB)`: oracle steps only increase
counters, so the bit is sticky. -/
private lemma inferSent_mono (gp : GameParams) (s s' : GameState (F ⊕ G) G G)
    (hA : s.tA ≤ s'.tA) (hB : s.tB ≤ s'.tB)
    (h : inferSent gp s = true) : inferSent gp s' = true := by
  cases hP : gp.challengedParty <;>
    · simp only [inferSent, hP, decide_eq_true_eq] at h ⊢
      refine ⟨h.1, h.2.1, ?_⟩
      exact le_trans h.2.2 (by first | exact hB | exact hA)

/-- Hybrid coupling invariant: `sH` is the projection of `sR`. -/
private def hybridRel (gp : GameParams) (a b : F)
    (sR sH : GameState (F ⊕ G) G G) : Prop :=
  sH = hybridProj (F := F) (gen := gen) gp a b sR

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- Base case: `init` has `lastAction = none`, which makes every
`windowRewrite` guard `false`, so `hybridProj gp a b init = init`. -/
private lemma hybridRel_init (gp : GameParams) (a b x₀ : F) :
    hybridRel (F := F) (G := G) (gen := gen) gp a b
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false)
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false) := by
  change _ = hybridProj (F := F) (gen := gen) gp a b _
  unfold hybridProj windowRewrite
  cases gp.challengedParty <;>
    simp [initGameState, ite_self]

/-! #### Counter / scalar preservation under `hybridProj`

`windowRewrite` only edits `stA`/`stB`; all other fields (counters,
`lastAction`, `lastRho?`, `lastKey?`, `corrupted?`) pass through unchanged. -/

omit [Fintype F] [SampleableType F] [SampleableType G] in
private lemma hybridProj_tA (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G) :
    (hybridProj (F := F) (gen := gen) gp a b s).tA = s.tA := by
  unfold hybridProj; split_ifs <;> rfl

omit [Fintype F] [SampleableType F] [SampleableType G] in
private lemma hybridProj_tB (gp : GameParams) (a b : F) (s : GameState (F ⊕ G) G G) :
    (hybridProj (F := F) (gen := gen) gp a b s).tB = s.tB := by
  unfold hybridProj; split_ifs <;> rfl

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- When `allowCorr` holds, both counters sit strictly below the challenge
window, so `hybridProj` is the identity. -/
private lemma hybridProj_eq_self_of_allowCorr (gp : GameParams) (a b : F)
    (s : GameState (F ⊕ G) G G) (h : allowCorr gp s = true) :
    hybridProj (F := F) (gen := gen) gp a b s = s := by
  simp only [allowCorr, decide_eq_true_eq] at h
  have hwin : inChallWindow gp s = false := by
    simp only [inChallWindow, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega
  unfold hybridProj; simp [hwin]

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- When `finishedA ∧ ΔCKA = 1`, we have `tA ≥ t* + 1`, which rules out both
`stA`-rewrite guards in `windowRewrite`; hence `stA` is preserved. -/
private lemma hybridProj_stA_of_finishedA (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (a b : F) (s : GameState (F ⊕ G) G G) (h : finishedA gp s = true) :
    (hybridProj (F := F) (gen := gen) gp a b s).stA = s.stA := by
  simp only [finishedA, finishedP, GameState.tP, decide_eq_true_eq, hΔ] at h
  unfold hybridProj
  split_ifs with _
  · unfold windowRewrite
    cases gp.challengedParty <;> cases s.stA <;>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
        ite_eq_right_iff, Sum.inl.injEq]
    all_goals (intros; omega)
  · rfl

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- Symmetric version: `finishedB ∧ ΔCKA = 1` preserves `stB`. -/
private lemma hybridProj_stB_of_finishedB (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (a b : F) (s : GameState (F ⊕ G) G G) (h : finishedB gp s = true) :
    (hybridProj (F := F) (gen := gen) gp a b s).stB = s.stB := by
  simp only [finishedB, finishedP, GameState.tP, decide_eq_true_eq, hΔ] at h
  unfold hybridProj
  split_ifs with _
  · unfold windowRewrite
    cases gp.challengedParty <;> cases s.stB <;>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
        ite_eq_right_iff, Sum.inl.injEq]
    all_goals (intros; omega)
  · rfl

/-! #### Oracle-step coupling: easy cases

`unif` is state-preserving and runs the same code on both sides; `corruptA`
and `corruptB` are state-preserving and their guards (`allowCorr ∨ finishedP`)
are preserved by `hybridProj`, as is the relevant `stP` component. -/

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- Uniform oracle: state unchanged, uniform output; `hrel` passes through. -/
private lemma hybridRel_query_unif (gp : GameParams) (a b : F)
    (t : unifSpec.Domain) (sR sH : GameState (F ⊕ G) G G)
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

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- `O-Corrupt-A`: state unchanged on both sides. The guard
`allowCorr ∨ finishedA` depends only on counters (preserved by `hybridProj`),
and in both disjuncts `(hybridProj sR).stA = sR.stA`, so the read matches. -/
private lemma hybridRel_query_corruptA (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (a b : F) (t : Unit) (sR sH : GameState (F ⊕ G) G G)
    (hrel : hybridRel (F := F) (G := G) (gen := gen) gp a b sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleCorruptA gp (F ⊕ G) G G t).run sR)
      ((oracleCorruptA gp (F ⊕ G) G G t).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  have hsHeq : sH = hybridProj (F := F) (gen := gen) gp a b sR := hrel
  have htA := hybridProj_tA (F := F) (gen := gen) gp a b sR
  have htB := hybridProj_tB (F := F) (gen := gen) gp a b sR
  have hallow_eq : allowCorr gp sH = allowCorr gp sR := by
    subst hsHeq; simp [allowCorr, htA, htB]
  have hfin_eq : finishedA gp sH = finishedA gp sR := by
    subst hsHeq; simp [finishedA, finishedP, GameState.tP, htA]
  have hstA_eq : allowCorr gp sR = true ∨ finishedA gp sR = true →
      sH.stA = sR.stA := by
    intro hguard
    subst hsHeq
    rcases hguard with ha | hf
    · rw [hybridProj_eq_self_of_allowCorr (F := F) (gen := gen) gp a b sR ha]
    · exact hybridProj_stA_of_finishedA (F := F) (gen := gen) gp hΔ a b sR hf
  have hvalue_eq :
      (if allowCorr gp sR || finishedA gp sR then some sR.stA else none) =
      (if allowCorr gp sH || finishedA gp sH then some sH.stA else none) := by
    rw [hallow_eq, hfin_eq]
    split_ifs with hc
    · rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact congrArg some (hstA_eq (Or.inl h)).symm
      · exact congrArg some (hstA_eq (Or.inr h)).symm
    · rfl
  have heq : ∀ s : GameState (F ⊕ G) G G,
      (oracleCorruptA gp (F ⊕ G) G G t).run s =
        (pure ((if allowCorr gp s || finishedA gp s then some s.stA else none), s) :
          ProbComp _) := by
    intro s; simp [oracleCorruptA]; split_ifs <;> rfl
  rw [heq sR, heq sH]
  refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ?_
  exact ⟨by rw [hvalue_eq], hrel⟩

omit [Fintype F] [SampleableType F] [SampleableType G] in
/-- `O-Corrupt-B`: symmetric to `hybridRel_query_corruptA`. -/
private lemma hybridRel_query_corruptB (gp : GameParams) (hΔ : gp.deltaCKA = 1)
    (a b : F) (t : Unit) (sR sH : GameState (F ⊕ G) G G)
    (hrel : hybridRel (F := F) (G := G) (gen := gen) gp a b sR sH) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((oracleCorruptB gp (F ⊕ G) G G t).run sR)
      ((oracleCorruptB gp (F ⊕ G) G G t).run sH)
      (fun pR pH =>
        pR.1 = pH.1 ∧ hybridRel (F := F) (G := G) (gen := gen) gp a b pR.2 pH.2) := by
  have hsHeq : sH = hybridProj (F := F) (gen := gen) gp a b sR := hrel
  have htA := hybridProj_tA (F := F) (gen := gen) gp a b sR
  have htB := hybridProj_tB (F := F) (gen := gen) gp a b sR
  have hallow_eq : allowCorr gp sH = allowCorr gp sR := by
    subst hsHeq; simp [allowCorr, htA, htB]
  have hfin_eq : finishedB gp sH = finishedB gp sR := by
    subst hsHeq; simp [finishedB, finishedP, GameState.tP, htB]
  have hstB_eq : allowCorr gp sR = true ∨ finishedB gp sR = true →
      sH.stB = sR.stB := by
    intro hguard
    subst hsHeq
    rcases hguard with ha | hf
    · rw [hybridProj_eq_self_of_allowCorr (F := F) (gen := gen) gp a b sR ha]
    · exact hybridProj_stB_of_finishedB (F := F) (gen := gen) gp hΔ a b sR hf
  have hvalue_eq :
      (if allowCorr gp sR || finishedB gp sR then some sR.stB else none) =
      (if allowCorr gp sH || finishedB gp sH then some sH.stB else none) := by
    rw [hallow_eq, hfin_eq]
    split_ifs with hc
    · rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact congrArg some (hstB_eq (Or.inl h)).symm
      · exact congrArg some (hstB_eq (Or.inr h)).symm
    · rfl
  have heq : ∀ s : GameState (F ⊕ G) G G,
      (oracleCorruptB gp (F ⊕ G) G G t).run s =
        (pure ((if allowCorr gp s || finishedB gp s then some s.stB else none), s) :
          ProbComp _) := by
    intro s; simp [oracleCorruptB]; split_ifs <;> rfl
  rw [heq sR, heq sH]
  refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ?_
  exact ⟨by rw [hvalue_eq], hrel⟩

/-- One-step simulation for the reduction/hybrid coupling.

Dispatches on the nine oracles via `cases_oracle`. The cases for `unif`,
`corruptA`, `corruptB` are closed by the dedicated helpers above (the code
runs identically on both sides, and `hybridProj` preserves everything the
oracles inspect). The remaining six cases — `sendA`, `recvA`, `sendB`,
`recvB`, `challA`, `challB` — require the identity/embedding/challenge
phase split described in the section header and are left as `sorry`. -/
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
  all_goals (simp only [reductionOracleImpl, hybridOracleImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr])
  · -- unif
    exact hybridRel_query_unif (F := F) (G := G) (gen := gen) gp a b t sR sH hrel
  · sorry -- sendA
  · sorry -- recvA
  · sorry -- sendB
  · sorry -- recvB
  · sorry -- challA
  · sorry -- challB
  · -- corruptA
    exact hybridRel_query_corruptA (F := F) (G := G) (gen := gen) gp hΔ a b t sR sH hrel
  · -- corruptB
    exact hybridRel_query_corruptB (F := F) (G := G) (gen := gen) gp hΔ a b t sR sH hrel

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

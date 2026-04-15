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
at most `ε`, then for any CKA adversary `𝒜`, challenge epoch `tStar`,
and challenged party `P ∈ {A, B}`:*

  `securityAdvantage(ddhCKA, 𝒜, ⟨tStar, 1, P⟩) ≤ ε`

*where `securityAdvantage = |Pr[b = b' | securityExp] - 1/2|` and `ΔCKA = 1`.
More precisely, there is an explicit DDH adversary
`ℬ = securityReduction ⟨tStar, 1, P⟩ 𝒜` such that
`securityAdvantage(ddhCKA, 𝒜, ⟨tStar, 1, P⟩) ≤ ddhGuessAdvantage(gen, ℬ)`,
with no multiplicative loss.*

### Why `ΔCKA = 1` is necessary and sufficient

`ΔCKA = 1` means corruption of party `Q` requires `tQ ≥ tStar + 1`: one
send after the challenge epoch. This is the smallest `ΔCKA` that works —
`ΔCKA = 0` would allow corrupting `P` immediately after the challenge,
revealing the challenge-epoch scalar.

Illustration with `P = A` challenged at `tA = tStar`:

```text
          A (challenged)                              B
          ──────────────                              ──
               │                                       │
  tA = t*      │  challA: z ←$ F                       │
               │  A stores z                           │
               │                                       │
               │────── ρ = gB, key = gT ──────────────▶│
               │                                       │  recvB: B stores gB
               │                                       │
               │                              tB = t*  │  sendB: x' ←$ F
               │                                       │  B stores x'
               │◀── ρ = x'•gen, key = x'•gB ──────────-│
               │  recvA                                │
               │                                       │
  tA = t*+1    │  sendA: y ←$ F                        │
               │  A stores y  (z overwritten)          │
               │                                       │
          ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
          finishedA (tA ≥ t*+1)     finishedB (tB ≥ t*+1)
          corruptA reveals y        corruptB reveals x'
```

At the point corruption is allowed, neither `stA` nor `stB` contains
information about the challenge key `gT`.

## Proof overview — reduction diagram

The adversary `𝒜` challenges exactly one party at epoch `t*`. We show the
case where `𝒜` calls `O-Chall-A` at `tA = t*`; the `O-Chall-B` case is
symmetric.

Given a DDH triple `(gen, gA, gB, gT)` with `gA = a • gen`,
`gB = b • gen`, and `gT = c • gen` where `c = a·b` (real) or `c` is uniform:

```text
 DDH Challenger                 DDH Adversary ℬ = securityReduction gp 𝒜
┌──────────────┐               ┌──────────────────────────────────────────────────────────┐
│              │ (gen,gA,gB,gT)│ sample x₀ ←$ F                                          │
│  gA = a•gen  │──────────────▶│ init A with g₀ := x₀ • gen, init B with x₀              │
│  gB = b•gen  │               │                                                          │
│  gT = c•gen  │               │ simulate CKA oracles for 𝒜 (honest except below):       │
│              │               │                                                          │
│  c = a·b     │               │          Honest CKA    │ Hybrid        │ Reduction       │
│  or random   │               │ ─────────────────────────────────────────────────────────│
│              │               │ O-Send-B, tB = t* - 1, state (xA, xA • gen):             │
│              │               │   y ←$ F               │               │                 │
│              │               │   ρ   = y • gen        │ ρ   = gA      │ ρ   = gA        │
│              │               │   key = y • xA • gen   │ key = xA • gA │ key = xA • gA   │
│              │               │   stB := y             │ stB := a      │ stB := y        │
│              │               │ ─────────────────────────────────────────────────────────│
│              │               │ recvA delivers ρ from above:                              │
│              │               │   stA := y • gen       │ stA := gA     │ stA := gA       │
│              │               │ ─────────────────────────────────────────────────────────│
│              │               │ O-Chall-A, tA = t*, state (stA, stB) from above:         │
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
private noncomputable def reductionSendB (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      if isOtherSendBeforeChall state then
        -- Embed: output (aG, xA·aG) instead of (y·G, y·xA·G).
        -- stA = .inl xA from A's last send; .inr branch unreachable.
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        -- Fresh y for stB only (output uses aG, not y).
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

/-- **O-Send-A** (modified for DDH reduction, symmetric to `reductionSendB`).
`() → Option (ρ : G, key : G)`.

At `tA = t*` (embedding epoch), with state `(stA, stB) = (h ∈ G, xB ∈ F)`:
- Reduction: `(ρ, key) = (aG, xB · aG)` — embeds DDH element `aG`
- Honest CKA: `(ρ, key) = (x · G, x · xB · G)` for `x ← $F`
- Same distribution since `a` is uniform like `x`
- Update: `(stA, stB, tA) ← (y ∈ F, xB, tA + 1)` for fresh `y ← $F`

All other epochs: delegates to `oracleSendA`. -/
private noncomputable def reductionSendA (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      if isOtherSendBeforeChall state then
        -- Embed: output (aG, xB·aG) instead of (x·G, x·xB·G).
        -- stB = .inl xB from B's last send; .inr branch unreachable.
        let xB := match state.stB with | .inl x => x | .inr _ => 0
        -- Fresh y for stA only (output uses aG, not y).
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

/-- **O-Chall-A** (modified for DDH reduction). `() → Option (ρ : G, key : G)`.

At `tA = t*`:
With state `(stA, stB) = (aG ∈ G, xB ∈ F)`:
- Reduction: `(ρ, key) = (gB, gT)` directly from DDH tuple
- Honest CKA: `(ρ, key) = (x · G, x · aG)` for `x ← $F`
- Real DDH: `(gB, gT) = (bG, b · aG)` by `smul_comm`; same distribution
- Random DDH: `gT = cG` for uniform `c`, matching `$ᵗ G`
- Update: `(stA, tA) ← (z ∈ F, tA + 1)` for fresh `z ← $F` (not `b`);
  `ΔCKA = 1` prevents corruption before `z` is overwritten -/
private noncomputable def reductionChallA (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA && isChallengeEpoch state then
      -- Fresh z for stA only; output is (gB, gT) from DDH tuple.
      let z ← liftM ($ᵗ F : ProbComp F)
      set { state with
        stA := (.inl z : F ⊕ G),
        lastRhoA := some gB, lastKeyA := some gT,
        lastAction := some .challA, tA := state.tA + 1 }
      return some (gB, gT)
    else pure none

/-- **O-Chall-B** (modified for DDH reduction, symmetric to `reductionChallA`).
`() → Option (ρ : G, key : G)`.

With state `(stA, stB) = (xA ∈ F, bG ∈ G)`:
- Output: `(ρ, key) = (gB, gT)` from DDH tuple
- Update: `(stB, tB) ← (z ∈ F, tB + 1)` for fresh `z ← $F` -/
private noncomputable def reductionChallB (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challB && isChallengeEpoch state then
      let z ← liftM ($ᵗ F : ProbComp F)
      set { state with
        stB := (.inl z : F ⊕ G),
        lastRhoB := some gB, lastKeyB := some gT,
        lastAction := some .challB, tB := state.tB + 1 }
      return some (gB, gT)
    else pure none

/-- Oracle implementation `R(g, aG, bG, gT)` for the DDH reduction.

Embeds the DDH tuple into the oracles for `challengedParty` (read from state):
- The other party's send embeds `aG` at `isOtherSendBeforeChall`
- The challenge oracle embeds `(gB, gT)` at `isChallengeEpoch`

All modified oracles are always present; each guards on `challengedParty`
internally, so only the relevant ones fire. -/
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
    let (b', _) ← (simulateQ (reductionOracleImpl gen gA gB gT) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false gp)
    return !b'

/-! ### Simulation: each DDH branch maps to the corresponding CKA branch

The goal is to show that the adversary `𝒜` has the same view whether it interacts with the
real CKA game or with the reduction's simulation.

The reduction `ℬ` returns `¬b'`. We show (see the module overview above):

    Pr[ℬ ⇒ 1 | DDH_real] = Pr[𝒜 ⇒ 0 | CKA^{b=0}]   … (real)
    Pr[ℬ ⇒ 1 | DDH_rand] = Pr[𝒜 ⇒ 0 | CKA^{b=1}]   … (rand)

The **real branch** uses three games (columns in the diagram above):

- `G_R`   — `securityReductionRealGame`:  `𝒜` vs `reductionOracleImpl` (Reduction)
- `G_H`   — `securityHybridGame`:       `𝒜` vs `hybridImpl`          (Hybrid)
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
    (simulateQ (reductionOracleImpl gen (a • gen) (b • gen) ((a * b) • gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false gp)
  return b'

/-- Unfold the real DDH branch of the reduction into the explicit helper game
`securityReductionRealGame`. -/
private lemma probOutput_ddhExpReal_securityReduction (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityReductionRealGame (F := F) (G := G) (gen := gen) gp adversary] := by
  unfold DiffieHellman.ddhExpReal securityReduction
  simpa [securityReductionRealGame, map_eq_bind_pure_comp] using
    (probOutput_not_map (m := ProbComp)
      (mx := securityReductionRealGame (F := F) (G := G) (gen := gen) gp adversary))

/-- The fixed-bit CKA security game with `b = false`, written explicitly with the
initial key sample exposed. -/
private noncomputable def securityExpFixedBitFalseGame (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (ckaSecurityImpl (ddhCKA F G gen)) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false gp)
  return b'

/-- Unfold the fixed-bit `b = false` branch into the explicit helper game
`securityExpFixedBitFalseGame`. -/
private lemma probOutput_securityExpFixedBit_false (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] =
    Pr[= false | securityExpFixedBitFalseGame (F := F) (G := G) (gen := gen) gp adversary] := by
  unfold CKAScheme.securityExpFixedBit securityExpFixedBitFalseGame ddhCKA
  simp [initGameState]

/-- Hybrid B-send used in the real-branch bridge.
At the special epoch before `challA`, it reuses the externally fixed DDH scalar
`a` both for the visible output and for B's next hidden state. This matches the
honest game instantiated with the corresponding challenge randomness, unlike
`reductionSendB`, which uses an independent fresh hidden scalar. -/
private noncomputable def hybridSendB (gen : G) (a : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      if isOtherSendBeforeChall state then
        -- At tB = t* - 1, state (stA, stB) = (xA, xA • gen).
        -- gA = a • gen
        let gA := a • gen
        -- xA is the scalar from A's last send
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        -- output: (ρ, key) = (a • gen, xA • a • gen)
        -- stB := a  (DDH scalar, not fresh y as in the reduction)
        set { state with
          stB := (.inl a : F ⊕ G), lastRhoB := some gA, lastKeyB := some (xA • gA),
          lastAction := some .sendB, tB := state.tB + 1 }
        return some (gA, xA • gA)
      else
        -- All other epochs: honest B-send
        match ← liftM (ddhCKA.send gen state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          set { state with
            stB := stB', lastRhoB := some ρ, lastKeyB := some key,
            lastAction := some .sendB, tB := state.tB + 1 }
          return some (ρ, key)
    else pure none

/-- Hybrid A-challenge used in the real-branch bridge.
At the challenge epoch, it reuses the externally fixed DDH scalar `b` as A's
post-challenge hidden state. This matches the honest game when the challenge
send samples `b`. -/
private noncomputable def hybridChallA (gen : G) (a b : F) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA && isChallengeEpoch state then
      -- At tA = t*, state (stA, stB) = (gA, y) from preceding recvA / sendB.
      -- gB = b • gen,  gT = (a · b) • gen
      let gB := b • gen
      let gT := (a * b) • gen
      -- output: (ρ, key) = (b • gen, (a · b) • gen)
      -- stA := b  (DDH scalar, not fresh z as in the reduction)
      set { state with
        stA := (.inl b : F ⊕ G),
        lastRhoA := some gB, lastKeyA := some gT,
        lastAction := some .challA, tA := state.tA + 1 }
      return some (gB, gT)
    else pure none

/-- Hybrid oracle implementation: same visible DDH embedding as
`reductionOracleImpl`, but the hidden states at the special B-send / A-challenge
epochs use the DDH scalars `a, b` instead of fresh randomness. -/
private noncomputable def hybridImpl (gen : G) (a b : F) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  (oracleUnif (F ⊕ G) G G
    + reductionSendA (F := F) gen (a • gen)
    + oracleRecvA (ddhCKA F G gen)
    + hybridSendB (F := F) gen a
    + oracleRecvB (ddhCKA F G gen))
  + hybridChallA (F := F) gen a b
  + reductionChallB (F := F) (b • gen) ((a * b) • gen)
  + oracleCorruptA (F ⊕ G) G G
  + oracleCorruptB (F ⊕ G) G G

/-- The explicit game induced by `hybridImpl`. -/
private noncomputable def securityHybridGame (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let x₀ ← $ᵗ F
  let (b', _) ←
    (simulateQ (hybridImpl (F := F) gen a b) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false gp)
  return b'

/-- State map `π : GameState → GameState` from `R`-states to `H`-states,
where `R := reductionOracleImpl(g, aG, bG, abG)` and `H := hybridImpl(g, a, b)`.

`R` and `H` agree on all outputs but diverge on hidden party state at two
embedding epochs: `R` draws fresh `y, z ←$ F` while `H` uses the DDH
scalars `a, b`. The map `π` substitutes the fresh scalars with the DDH ones:

- `stB` window (`tB = t*`, after sendB): `π(stB) = a` where `stB = y` in `R`
- `stA` window (`tA = t* + 1`, after challA): `π(stA) = b` where `stA = z` in `R`

All other fields (outputs, counters, flags) pass through unchanged. -/
private noncomputable def hybridProj (a b : F)
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

Let `π := hybridProj a b` (state projection),
`R := reductionOracleImpl(g, aG, bG, abG)` (concrete reduction oracles),
`H := hybridImpl(g, a, b)` (hybrid oracles). Then:

    `(id × π)(R(q, s)) = H(q, π(s))`

for any oracle query `q` and game state `s`. -/
private lemma hybridProj_query_map_eq (gp : GameParams) (a b : F)
    (t : (ckaSecuritySpec (F ⊕ G) G G).Domain)
    (s : GameState (F ⊕ G) G G) :
    Prod.map id (hybridProj (F := F) a b) <$>
      ((reductionOracleImpl gen (a • gen) (b • gen) ((a * b) • gen)) t).run s =
    ((hybridImpl (F := F) gen a b) t).run
      (hybridProj (F := F) a b s) := by
  sorry

/-- First half of the real-branch bridge: the concrete reduction may differ from
`hybridImpl` on hidden intermediate state, but these differences remain
unobservable under strict healing (`ΔCKA = 1`). -/
private lemma securityReduction_real_to_hybrid (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRealGame (F := F) (G := G) (gen := gen) gp adversary] =
    Pr[= false | securityHybridGame (F := F) (G := G) (gen := gen) gp adversary] := by
  unfold securityReductionRealGame securityHybridGame
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro a
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro b
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) false ?_
  intro x₀
  have hinit :
      hybridProj (F := F) a b
        (initGameState (.inr (x₀ • gen)) (.inl x₀) false gp) =
      initGameState (.inr (x₀ • gen)) (.inl x₀) false gp := by
    simp [hybridProj, initGameState]
  have hrun' :=
    OracleComp.ProgramLogic.Relational.run'_simulateQ_eq_of_query_map_eq
      (impl₁ := reductionOracleImpl gen (a • gen) (b • gen) ((a * b) • gen))
      (impl₂ := hybridImpl (F := F) gen a b)
      (proj := hybridProj (F := F) a b)
      (hproj := hybridProj_query_map_eq (F := F) (G := G) (gen := gen) gp a b)
      adversary
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false gp)
  rw [hinit] at hrun'
  exact congrArg (fun mx => Pr[= false | mx]) hrun'

/-- Second half of the real-branch bridge: `hybridImpl` is the honest
fixed-bit-false game with the two special challenge scalars sampled explicitly
up front. -/
private lemma securityReduction_hybrid_to_honest (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityHybridGame (F := F) (G := G) (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitFalseGame (F := F) (G := G) (gen := gen) gp adversary] := by
  sorry

/-- The core bridge for the real branch: the explicit real-DDH reduction game
matches the explicit fixed-bit CKA game with `b = false`. -/
private lemma securityReduction_real_bridge (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= false | securityReductionRealGame (F := F) (G := G) (gen := gen) gp adversary] =
    Pr[= false | securityExpFixedBitFalseGame (F := F) (G := G) (gen := gen) gp adversary] := by
  rw [securityReduction_real_to_hybrid (F := F) (G := G) (gen := gen) gp adversary]
  exact securityReduction_hybrid_to_honest (F := F) (G := G) (gen := gen) gp adversary

/-- **Real-branch lemma.**
`Pr[ℬ outputs true | real DDH] = Pr[𝒜 guesses false | CKA b = false]`. -/
lemma securityReduction_real (gp : GameParams)
    (adversary : SecurityAdversary (F ⊕ G) G G) :
    Pr[= true | ddhExpReal gen (securityReduction gp adversary)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false gp] := by
  rw [probOutput_ddhExpReal_securityReduction, probOutput_securityExpFixedBit_false]
  exact securityReduction_real_bridge (F := F) (G := G) (gen := gen) gp adversary

/-- **Random-branch lemma.**
`Pr[ℬ outputs true | random DDH] = Pr[𝒜 guesses false | CKA b = true]`.
Needs bijectivity of `· • gen` to couple `c • gen` with `$ᵗ G`. -/
lemma securityReduction_rand (gp : GameParams)
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
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G)
    (ε : ℝ)
    (hddh : ∀ adv : DDHAdversary F G,
      ddhGuessAdvantage gen adv ≤ ε) :
    securityAdvantage (ddhCKA F G gen) adversary gp ≤ ε :=
  calc securityAdvantage (ddhCKA F G gen) adversary gp
      ≤ ddhGuessAdvantage gen (securityReduction gp adversary) :=
        security gp hg adversary
    _ ≤ ε := hddh _

end ddhCKA

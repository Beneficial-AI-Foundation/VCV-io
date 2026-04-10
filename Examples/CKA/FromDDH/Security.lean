import Examples.CKA.FromDDH.Construction

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

The challB case is symmetric with A/B roles swapped (see `reductionImplB`).
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

**Corruption safety** (`ΔCKA = 1`). After the challenge:
- Party A's state from epoch `tStar + 1` is `.inl x'` (fresh, independent of `a,b`).
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

/-- Modified B-send oracle for the DDH reduction.

At epoch `tB = tStar - 1` (the send immediately before A's potential challenge),
replaces the honest protocol message with `gA = a • gen` (from the DDH
challenge) and computes the returned key as `xA • gA`, where `xA` is A's
current exponent (from A's last send). A fresh
scalar is still sampled for B's state evolution.

At all other B-send epochs, delegates to the standard `oracleSendB`. -/
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
        let (key, ρ, stB') ← liftM (ddhCKA.send gen state.stB)
        set { state with
          stB := stB', lastRhoB := some ρ, lastKeyB := some key,
          lastAction := some .sendB, tB := state.tB + 1 }
        return some (ρ, key)
    else pure none

/-- Symmetric A-send modification for the challB reduction.

At epoch `tA = tStar` (the A-send immediately before B's potential challenge),
replaces the honest protocol message with `gA = a • gen` (from the DDH
challenge) and computes the returned key as `xB • gA`, where `xB` is B's
current exponent. A fresh scalar is still sampled for A's state evolution.

At all other A-send epochs, delegates to the standard `oracleSendA`. -/
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
        let (key, ρ, stA') ← liftM (ddhCKA.send gen state.stA)
        set { state with
          stA := stA', lastRhoA := some ρ, lastKeyA := some key,
          lastAction := some .sendA, tA := state.tA + 1 }
        return some (ρ, key)
    else pure none

/-- Modified A-challenge oracle for the challA reduction.

Replaces the honest send computation with the DDH challenge: returns
`(gB, gT)` as `(message, key)`. A fresh scalar `z` seeds A's
post-challenge state `.inl z`, matching the honest game's distribution
(important for corruption safety with `ΔCKA = 1`).

When the DDH triple is real (`gT = (a * b) • gen`), the returned pair
`(gB, gT) = (b • gen, (a * b) • gen)` matches the honest distribution
`(x • gen, x • gA) = (x • gen, (x * a) • gen)` for fresh `x`,
since `b` is uniform just like `x`. -/
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

/-- Symmetric B-challenge oracle for the challB reduction.

Replaces the honest B-send computation with the DDH challenge: returns
`(gB, gT)` as `(message, key)`. Symmetric to `reductionChallA` with
A/B roles swapped. -/
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

/-- Oracle implementation for the DDH reduction. Replaces all four
send/challenge oracles with their DDH-embedding variants:
- `oracleSendA` → `reductionSendA` (embeds `gA` at the send before challB)
- `oracleSendB` → `reductionSendB` (embeds `gA` at the send before challA)
- `oracleChallA` → `reductionChallA` (embeds `gB, gT` at `tStar`)
- `oracleChallB` → `reductionChallB` (embeds `gB, gT` at `tStar`)

Only one challenge oracle fires (the adversary calls either challA or challB
at epoch `tStar`). -/
private noncomputable def reductionImpl (gen gA gB gT : G) :
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
2. Runs the adversary against `reductionImpl`, which embeds `gA` into
   the send oracles and `(gB, gT)` into the challenge oracles for both
   parties A and B.
3. Outputs `!b'` (negated CKA guess) to align bit conventions. -/
noncomputable def securityReduction
    (adversary : SecurityAdversary (F ⊕ G) G G)
    (tStar : ℕ) : DDHAdversary F G :=
  fun gen gA gB gT => do
    let x₀ ← $ᵗ F
    let (b', _) ← (simulateQ (reductionImpl gen gA gB gT) adversary).run
      (initGameState (.inr (x₀ • gen)) (.inl x₀) false tStar 1)
    return !b'

/-! ### Simulation: each DDH branch maps to the corresponding CKA branch

Using the generic `securityExpFixedBit` (defined in `Defs.lean`), we show
that the two branches of the DDH experiment (real and random) correspond
exactly to the two branches of the CKA security game (`b = false` and
`b = true`):

- **Real DDH → CKA with `b = false`** (`securityReduction_real`):
  When the DDH triple is real, the reduction's oracle simulation produces
  exactly the same output distribution as the CKA game with real keys.

- **Random DDH → CKA with `b = true`** (`securityReduction_rand`):
  When the DDH triple is random, the simulation matches the CKA game with
  random keys (using bijectivity of `· • gen` to equate `c • gen` with `$ᵗ G`).

Combined with the standard decomposition of both games over a fair coin
(`ddhExp_probOutput_sub_half` for DDH, `securityExp_toReal_sub_half` for CKA),
this yields `ddhGuessAdvantage(gen, ℬ) = securityAdvantage(ddhCKA, 𝒜, tStar, 1)`.
-/

/-- **Real-branch lemma.**
`Pr[ℬ outputs true | real DDH] = Pr[𝒜 guesses false | CKA b = false]`.

Proof outline: (1) handle `!b'` via `probOutput_not_map`, (2) reorder DDH
samples past `x₀` via `probOutput_bind_bind_swap`, (3) apply
`evalDist_simulateQ_run'_eq_of_bisim` with a state relation coupling the
reduction's DDH-embedded oracles to the honest game's oracles, using
`smul_comm` for the per-query coupling at the modified send/challenge epochs. -/
lemma securityReduction_real
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ) :
    Pr[= true | ddhExpReal gen (securityReduction adversary tStar)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false tStar 1] := by
  sorry

/-- **Random-branch lemma.**
`Pr[ℬ outputs true | random DDH] = Pr[𝒜 guesses false | CKA b = true]`.

Same structure as `securityReduction_real`, but uses bijectivity of `· • gen`
to couple the DDH random element `c • gen` with `$ᵗ G`. -/
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

**Corruption safety** (`ΔCKA = 1`). After the challenge:
- The challenged party's state at `tStar + 1` is `.inl x'` (fresh, independent of `a,b`).
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

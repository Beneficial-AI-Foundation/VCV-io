import Examples.CKA.FromDDH.Construction

/-!
# CKA from DDH — Security Proof

Security reduction from DDH to CKA key-indistinguishability,
following [ACD19, Theorem 3].
https://eprint.iacr.org/2018/1037.pdf

## Main result

**Theorem** (`ddhCKA_security`). *Let `G` be a group with generator `gen` such
that `· • gen : F → G` is bijective. If every DDH adversary has guess-advantage
at most `ε`, then for any CKA adversary `𝒜` that uses `challA` at epoch `tStar`,
and any `tStar : ℕ`:*

  `securityAdvantage(ddhCKA, 𝒜, tStar, ΔCKA := 1) ≤ ε`

*where `securityAdvantage = |Pr[b = b' | securityExp] - 1/2|`.
More precisely, there is an explicit DDH adversary `ℬ` = `securityReduction 𝒜 tStar`
such that `securityAdvantage(ddhCKA, 𝒜, tStar, 1) ≤ ddhGuessAdvantage(gen, ℬ)`,
with no multiplicative loss.

*TODO*: The restriction to `challA` is WLOG since `sendA = sendB` in the DDH-CKA
scheme: an adversary using `challB` can be transformed into one using `challA` by
swapping the roles of parties A and B.*

## Proof overview — reduction diagram

WLOG assume party A is challenged at epoch `tStar` (the case for party B is
symmetric since `sendA = sendB`).  Given a DDH triple `(gen, gA, gB, gT)` with
`gA = a • gen`, `gB = b • gen`, and `gT = c • gen` where `c = a·b` (real) or
`c` random:

```text
 DDH Challenger                       DDH Adversary ℬ = securityReduction(𝒜, tStar)
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

**Bit convention.** DDH `bit = true` means real triple; CKA `b = true` means
random key. The reduction outputs `!b'` to align these conventions.

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
replaces the honest protocol message with `gA` and computes the returned key as
`xA • gA`, where `xA` is A's current exponent (from A's last send). A fresh
scalar is still sampled for B's state evolution.

At all other B-send epochs, delegates to the standard `oracleSendB`.

**Distribution argument.** The pair `(gA, xA • gA)` returned to the adversary
has the same distribution as the honest `(y • gen, y • h)` for fresh `y`:
both are `(α • gen, (α · xA) • gen)` for uniform `α` (using `Field F`). -/
private noncomputable def reductionSendB (gen gA : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      if state.tB + 1 == state.tStar then
        let xA := match state.stA with | .inl x => x | .inr _ => 0
        let y ← liftM ($ᵗ F : ProbComp F)
        set { state with
          stB := .inl y, lastRhoB := some gA, lastKeyB := some (xA • gA),
          lastAction := some .sendB, tB := state.tB + 1 }
        return some (gA, xA • gA)
      else
        let (key, ρ, stB') ← liftM (ddhCKA.send gen state.stB)
        set { state with
          stB := stB', lastRhoB := some ρ, lastKeyB := some key,
          lastAction := some .sendB, tB := state.tB + 1 }
        return some (ρ, key)
    else pure none

/-- Modified A-challenge oracle for the DDH reduction.

Replaces the honest send computation with the DDH challenge: returns
`(gB, gT)` as `(message, key)`. The state is set to a dummy `.inl 0`
(overwritten at the next `recv` to `.inr gB`, which is correct for
subsequent honest sends).

When the DDH triple is real (`gT = (a * b) • gen`), the returned pair
`(gB, gT) = (b • gen, (a * b) • gen)` matches the honest distribution
`(x • gen, x • gA) = (x • gen, (x * a) • gen)` for fresh `x`,
since `b` is uniform just like `x`. -/
private noncomputable def reductionChallA (gB gT : G) :
    QueryImpl (Unit →ₒ Option (G × G)) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA && state.tA == state.tStar then
      set { state with
        stA := (.inl (0 : F) : F ⊕ G),
        lastRhoA := some gB, lastKeyA := some gT,
        lastAction := some .challA, tA := state.tA + 1 }
      return some (gB, gT)
    else pure none

/-- Oracle implementation for the DDH reduction. Identical to the standard
`ckaSecurityImpl` except:
- `oracleSendB` is replaced by `reductionSendB` (embeds `gA` at `tStar - 1`)
- `oracleChallA` is replaced by `reductionChallA` (embeds `gB, gT` at `tStar`)

All other oracles (sendA, recvA, recvB, challB, corruptA, corruptB, uniform)
are unchanged.

After the challenge, B's state is updated to `.inr gB` by the standard recv
oracle, so `oracleSendB` at `tStar` computes `x' • gB` honestly — matching
the paper's `T_{t*+1} = g^{x'}` and `I_{t*+1} = g^{bx'}`. -/
private noncomputable def reductionImpl (gen gA gB gT : G) :
    QueryImpl (ckaSecuritySpec (F ⊕ G) G G) (StateT (GameState (F ⊕ G) G G) ProbComp) :=
  (oracleUnif (F ⊕ G) G G
    + oracleSendA (ddhCKA F G gen)
    + oracleRecvA (ddhCKA F G gen)
    + reductionSendB (F := F) gen gA
    + oracleRecvB (ddhCKA F G gen))
  + reductionChallA (F := F) gB gT
  + oracleChallB (ddhCKA F G gen)
  + oracleCorruptA (F ⊕ G) G G
  + oracleCorruptB (F ⊕ G) G G

/-- DDH adversary obtained by reduction from a CKA security adversary
[ACD19, Theorem 3].

Given a DDH triple `(gen, gA, gB, gT)`, the reduction:
1. Initialises the CKA game honestly: `x₀ ← $ᵗ F`.
2. Runs the adversary against `reductionImpl`, which modifies two oracles:
   - B-send at `tB = tStar - 1`: message `= gA`, key `= xA • gA`.
   - A-chall at `tA = tStar`: message `= gB`, key `= gT`.
3. Outputs `!b'` (negated CKA guess) to align bit conventions.

**Epoch `tStar + 1` needs no modification**: after B receives `gB`, B's state
is `.inr gB`, so the honest send already produces `(x' • gen, x' • gB)`,
matching the paper's `T_{t*+1} = g^{x'}` and `I_{t*+1} = g^{bx'}`.

This handles the case where A is challenged (`challA` at `tA = tStar`).
The symmetric case (`challB`) is analogous with A/B roles swapped. -/
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

/-- An adversary *challenges through party A* if it calls `challA` (not `challB`)
at epoch `tStar`. This is without loss of generality when `sendA = sendB`, as in
DDH-CKA: an adversary using `challB` can be transformed into one using `challA`
by swapping the roles of parties A and B. -/
def ChallengesA (_adversary : SecurityAdversary (F ⊕ G) G G) : Prop := sorry

/-- **Real-branch lemma.** With a real DDH triple, the reduction perfectly
simulates the CKA game with `b = false` (real key).

The key identity is at stage ③: `gT = (a·b) • gen = b • (a • gen) = b • gA`
by `smul_comm`, which matches the honest CKA key `x • gA` for the "effective
exponent" `x = b`.

`Pr[ℬ outputs true | real DDH] = Pr[𝒜 guesses false | CKA b = false]` -/
lemma securityReduction_real
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ)
    (hA : ChallengesA adversary) :
    Pr[= true | ddhExpReal gen (securityReduction adversary tStar)] =
    Pr[= false | securityExpFixedBit (ddhCKA F G gen) adversary false tStar 1] := by
  sorry

/-- **Random-branch lemma.** With a random DDH triple, the reduction perfectly
simulates the CKA game with `b = true` (random key).

Bijectivity of `· • gen` is needed here: the DDH random branch provides
`c • gen` for `c ← $ᵗ F`, while the CKA game samples the random challenge
key from `$ᵗ G` directly. Bijectivity ensures these have the same distribution.

`Pr[ℬ outputs true | random DDH] = Pr[𝒜 guesses false | CKA b = true]` -/
lemma securityReduction_rand
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ)
    (hA : ChallengesA adversary) :
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
- Party A's state from epoch `tStar + 1` is `.inl x'` (fresh, independent of `a,b`).
- Party B's state from epoch `tStar` is `.inr gB` (public DDH component).
-/

/-- **DDH-CKA security (per-adversary form)** [ACD19, Theorem 3].

For any CKA adversary `𝒜` that challenges through party A, the CKA advantage
equals the DDH guess-advantage of the reduction `ℬ = securityReduction 𝒜 tStar`:

  `securityAdvantage(ddhCKA, 𝒜, tStar, 1) ≤ ddhGuessAdvantage(gen, ℬ)`

The symmetric case where `𝒜` challenges through party B is analogous. -/
theorem security
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G) (tStar : ℕ)
    (hA : ChallengesA adversary) :
    securityAdvantage (ddhCKA F G gen) adversary tStar 1 ≤
      ddhGuessAdvantage gen (securityReduction adversary tStar) := by
  sorry

/-- **DDH-CKA security (quantitative form)** [ACD19, Theorem 3].

If the DDH assumption holds in `G` with guess-advantage at most `ε` for every
adversary, then for any CKA adversary `𝒜` that challenges through party A:

  `securityAdvantage(ddhCKA, 𝒜, tStar, 1) ≤ ε` -/
theorem ddhCKA_security
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : SecurityAdversary (F ⊕ G) G G)
    (tStar : ℕ) (ε : ℝ)
    (hA : ChallengesA adversary)
    (hddh : ∀ adv : DDHAdversary F G,
      ddhGuessAdvantage gen adv ≤ ε) :
    securityAdvantage (ddhCKA F G gen) adversary tStar 1 ≤ ε :=
  calc securityAdvantage (ddhCKA F G gen) adversary tStar 1
      ≤ ddhGuessAdvantage gen (securityReduction adversary tStar) :=
        security hg adversary tStar hA
    _ ≤ ε := hddh _

end ddhCKA

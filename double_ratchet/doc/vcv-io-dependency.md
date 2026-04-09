# VCV-io Dependency Analysis

Should we keep VCV-io as a dependency, copy the infrastructure we need,
or rewrite from scratch using Mathlib directly?

## The Mathematical Observation

A cyclic group of prime order p IS ℤ/pℤ, canonically. The whole
`Module F G` + `hg : Bijective` dance is just saying "G ≅ F via a ↦ a • g"
with extra steps.

The reason VCV-io uses this API: they want to keep F (scalars/exponents) and
G (group elements) as separate types so you can instantiate G with an
elliptic curve group where the representations differ (Curve25519 points vs.
ZMod p scalars). The bijectivity hypothesis is the tax on that abstraction.

For pure math, you could just write DDH directly in ZMod p: "distinguish
(a, b, a*b) from (a, b, c) for uniform a, b, c ∈ ZMod p." No Module, no
bijectivity, no generator. That's cleaner and equivalent.

## What We Actually Import

The current project has 9 local Lean files under `DoubleRatchet/`. Of those,
7 directly import VCV-io modules, and together they use 8 distinct upstream
modules.

The repo also contains a `FromVCVio/` snapshot of selected upstream files for
local reference, but the build still uses the pinned Lake dependency
`VCV-io` at commit `a3d6c41`.

```
CKA/Defs.lean              → VCVio.OracleComp.ProbComp
                             VCVio.OracleComp.Constructions.SampleableType
CKA/SecurityGame.lean      → VCVio.EvalDist.Bool
                             VCVio.OracleComp.Constructions.SampleableType
CKA/Figure3Game.lean       → VCVio.OracleComp.SimSemantics.Append
                             VCVio.OracleComp.HasQuery
                             VCVio.EvalDist.Bool
CKA/MultiEpochGame.lean    → VCVio.OracleComp.Constructions.SampleableType
Constructions/DDHCKA.lean  → VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
Theorems/Reduction.lean    → VCVio.OracleComp.SimSemantics.PreservesInv
Theorems/AsymptoticSecurity.lean
                           → VCVio.CryptoFoundations.Asymptotics.Security
```

## What We Actually Use From Each Import

### 1. `VCVio.OracleComp.ProbComp`

We use:
- `ProbComp α` — type abbreviation for `OracleComp unifSpec α`
- `do` notation, `pure`, `>>=` on ProbComp

This is a **free monad** over oracle queries, specialized to uniform sampling.
Under the hood: `OracleComp` is a polynomial-functor free monad with an
"oracle spec" indexing the available queries. `unifSpec` provides uniform
sampling from `Fin n`.

What we actually need: a probability monad. Mathlib has `PMF` (probability
mass functions) but no monadic `do` notation for it. VCV-io's value is
providing `ProbComp` with `do` notation + probability evaluation.

### 2. `VCVio.EvalDist.Bool` (imports chain)

We use:
- `Pr[= x | computation]` — probability notation
- `ENNReal.toReal` — converting probabilities to ℝ for the advantage

This is the "evaluation semantics" that interprets `ProbComp α` as an actual
probability distribution and lets you compute `Pr[event | computation]`.

Transitive chain: `EvalDist.Bool` → `EvalDist.Defs.Basic` → `OracleComp.EvalDist`
→ Mathlib's SPMF/PMF infrastructure.

### 3. `VCVio.OracleComp.Constructions.SampleableType`

We use:
- `SampleableType β` — typeclass for types with uniform sampling
- `$ᵗ T` — notation for `uniformSample T`
- Instances for `Bool`, `Fin n`, products, `ZMod`

This is the bridge between "sample uniformly from type T" and the oracle
framework. It provides `selectElem : ProbComp β` that samples uniformly.

### 4. `VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman`

We use:
- `DDHAdversary F G` — type alias `G → G → G → G → ProbComp Bool`
- `ddhExpReal g adversary` — real DDH game
- `ddhExpRand g adversary` — random DDH game
- `ddhDistAdvantage g adversary` — `|Pr[real=1] - Pr[rand=1]|`

We do NOT use:
- `DLogAdversary`, `dlogExp` — discrete log
- `CDHAdversary`, `cdhExp` — computational DH
- `ddhExp` (single-game formulation), `ddhGuessAdvantage`
- `ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage` — relating formulations
- `dlogGenerable`, `NondegenerateGenerator` — cyclic group helpers
- `cdhToDDHReduction` and related theorems — CDH-to-DDH reduction

### 5. `VCVio.OracleComp.SimSemantics.Append` and `VCVio.OracleComp.HasQuery`

We use:
- `QueryImpl` addition `(unifImpl + gameImpl)` to combine uniform sampling with
  the game oracle implementation
- `HasQuery.toQueryImpl` to turn `unifSpec` sampling into an executable query
  implementation inside the Figure 3 experiment

These imports are what make the current adaptive Figure 3 game convenient to
write in `OracleComp` style. They are not incidental anymore: both
`CKA/Figure3Game.lean` and the DDH reduction use them directly.

### 6. `VCVio.OracleComp.SimSemantics.PreservesInv`

We use:
- `QueryImpl.PreservesInv`
- the stateful invariant machinery around `StateT σ ProbComp`

This supports the current `Reduction.redQueryImpl_preservesRedInv` statement:
the symbolic reduction uses `stateToConc : ... → Option (G ⊕ F)`, and the proof
obligation is precisely that valid corruption traces never reach the `none`
branches for symbolic secrets.

### 7. `VCVio.CryptoFoundations.Asymptotics.Security`

We use:
- `SecurityGame`
- `SecurityGame.secureAgainst`
- `SecurityGame.secureAgainst_of_reduction`

This is the asymptotic wrapper used by `Theorems/AsymptoticSecurity.lean` for
both the single-epoch warmup and the Figure 3 game.

## What VCV-io Brings Transitively

VCV-io depends on Mathlib v4.28.0. Through the imports above, we pull in:
- The `OracleComp` core plus the `SimSemantics` layer (`QueryImpl`,
  `simulateQ`, append/lifting combinators, invariant framework)
- `EvalDist` probability semantics
- `CryptoFoundations` DDH definitions and asymptotic security wrappers
- Mathlib's `Probability.ProbabilityMassFunction` module
- Mathlib's `MeasureTheory` (transitively, for SPMF)
- `ToMathlib/` extensions (~1K lines of extra Mathlib lemmas)

The total VCV-io surface is still large. But the project now directly relies on
more than just a tiny `ProbComp` front-end: the current skeleton uses a real
slice of VCV-io's oracle semantics, DDH games, invariant framework, and
asymptotic security API.

## Three Options

### Option A: Keep VCV-io (status quo)

**Pros:**
- Already working, builds clean
- DDH definitions are battle-tested (used in ElGamal proof, CDH reduction)
- The current Figure 3 game and reduction already use VCV-io's `OracleComp`
  simulation style directly (`QueryImpl`, `simulateQ`, append/lift machinery)
- The invariant framework in `SimSemantics.PreservesInv` matches the current
  reduction proof obligations
- If we later formalize Theorem 6 (full SM), VCV-io's KEM, PRF, PRG
  definitions and the program logic tactics become valuable
- Proven lemmas available (e.g., `ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage`)

**Cons:**
- Pulls a large dependency surface for a focused project
- We don't control the API; changes upstream could break us
- The `Module F G` + bijectivity abstraction is heavier than needed
- `OracleComp` free-monad machinery is heavier than a bespoke concrete encoding
- Lake dependency management pain (as we experienced)

**Effort:** 0 (done)

### Option B: Vendor the currently used VCV-io slice, still depend on Mathlib

Instead of depending on the full external package, vendor just the slice the
current formalization actually uses:
1. `ProbComp`, `OracleSpec`, `OracleComp`, and the sampling interface
2. `QueryImpl`, `simulateQ`, append/lift combinators, and `HasQuery`
3. The invariant layer used by `PreservesInv`
4. Probability evaluation / `Pr[= x | comp]` notation
5. DDH definitions
6. `SecurityGame` and the reduction wrapper theorem

The DDH definitions become dramatically simpler:

```lean
-- Instead of Module F G + bijectivity:
variable (p : ℕ) [Fact (Nat.Prime p)]

def DDHAdversary := ZMod p → ZMod p → ZMod p → ProbComp Bool

def ddhRealExp (adversary : DDHAdversary p) : ProbComp Bool := do
  let a ← $ᵗ (ZMod p)
  let b ← $ᵗ (ZMod p)
  adversary a b (a * b)

def ddhRandExp (adversary : DDHAdversary p) : ProbComp Bool := do
  let a ← $ᵗ (ZMod p)
  let b ← $ᵗ (ZMod p)
  let c ← $ᵗ (ZMod p)
  adversary a b c
```

No generator, no Module, no bijectivity hypothesis. The CKA construction
becomes:

```lean
def ddhCKA (p : ℕ) [Fact (Nat.Prime p)] : CKAScheme ... where
  init k := pure (k, k)         -- both parties know k ∈ ZMod p
  send h := do
    let x ← $ᵗ (ZMod p)
    pure (x, x, x * h)          -- msg = x, output = x * h
  recv x msg := pure (msg, x * msg)
```

**Pros:**
- Mathematically transparent: DDH is just multiplication in ZMod p
- No bijectivity hypothesis needed
- No `Module F G` indirection
- Still use Mathlib for `ZMod`, `PMF`, algebraic lemmas
- More control over the exact API surface than depending on all of VCV-io

**Cons:**
- No longer a tiny extraction: the current Figure 3 skeleton depends on oracle
  semantics and invariant machinery, not just `ProbComp`
- Need either to vendor a nontrivial local slice of VCV-io or redesign parts of
  the current game/reduction encoding
- Lose direct connection to upstream VCV-io lemmas and examples
- If we later want EC group instantiations, we'd need to add abstraction back
- Mathlib dependency remains (for ZMod, PMF, etc.)

**Effort:** moderate; substantially larger than the original single-epoch-only estimate

**Risk:** The hard part is no longer just `ProbComp`. The current Figure 3
formalization is already phrased in VCV-io's oracle-simulation style, so a
dependency reduction now touches `simulateQ`, query composition, invariants, and
the asymptotic wrapper as well.

### Option C: Minimal, Mathlib-only

Same as Option B but also avoid building a custom ProbComp monad.
Use Mathlib's `PMF` directly as a type, define games as PMF-valued functions.

```lean
def DDHRealDist (p : ℕ) [Fact (Nat.Prime p)] : PMF (ZMod p × ZMod p × ZMod p) :=
  PMF.uniformOfFintype (ZMod p) >>= fun a =>
  PMF.uniformOfFintype (ZMod p) >>= fun b =>
  PMF.pure (a, b, a * b)
```

**Pros:**
- Zero external dependencies beyond Mathlib
- Maximally transparent
- Mathlib's PMF has good automation (simp lemmas, etc.)

**Cons:**
- Would force a redesign of the current Figure 3 game and reduction, since they
  are presently encoded in `OracleComp` / `QueryImpl` style
- PMF doesn't have nice do-notation in Lean 4 (awkward bind chains)
- All VCV-io probability lemmas and oracle-composition infrastructure need
  re-proving or replacing from Mathlib primitives
- No `Pr[= x | comp]` notation without building it
- Higher effort for less ergonomic code

**Effort:** high; this is now a redesign, not just a dependency cleanup

## What VCV-io Might Be Useful For Later

If we formalize beyond Theorem 3:
- **KEM definitions** (`KeyEncapMech.lean`) — for Theorem 2 (KEM → CKA)
- **PRF definitions** (`PRF.lean`) — for PRF-PRNG (Section 4.3)
- **PRG definitions** (`PRG.lean`) — for FS-AEAD (Section 4.2)
- **Program logic tactics** (`rvcstep`, `vcstep`) — for distribution proofs
- **Asymptotic security** (`Security.lean`) — for runtime modeling
- **ElGamal example** — reference for DDH-based proofs

## Current Recommendation

**Keep VCV-io for now.**

The concrete risk of rewriting is the ProbComp monad: VCV-io's probability
evaluation semantics (evalDist, support tracking, SPMF) are ~2K lines of
subtle code. We need these for the distribution equality proofs (the sorry's).
With the current Figure 3 skeleton, the cost is actually broader still: the
project now relies on VCV-io's oracle-simulation and invariant framework as
well, so replacing the dependency is no longer a local cleanup.

However, if VCV-io's API friction becomes blocking (e.g., the Module F G
abstraction makes proofs harder than they should be), a focused vendoring pass
is still viable. The DDH simplification to ZMod p remains attractive for
mathematical clarity, but it should be treated as a deliberate rewrite of the
current skeleton rather than a quick dependency trim.

**Concrete trigger for switching:** if the `Module F G` abstraction or VCV-io
oracle APIs become the dominant blocker during proof completion, switch to a
scoped vendoring/rewrite plan before investing heavily in those proofs.

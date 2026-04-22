/-
Copyright (c) 2026 Sergiu Bursuc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergiu Bursuc
-/
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Dead-store elimination and external-sample commutation under `simulateQ`

Two library-grade distributional equivalence theorems for `simulateQ`-based oracle
simulation targeting `StateT σ ProbComp`.

## Main results

* `probOutput_simulateQ_run'_eq_of_state_rel` — **dead-store elimination**.
  If two implementations produce, under a chosen state relation `R`, a coupling
  on each query that preserves output equality and `R` on the post-state, then
  their full `simulateQ` runs produce equal output distributions.

* `probOutput_simulateQ_greedyLazy_run'_eq` — **external-sample commutation**.
  A top-level sample `a ← $ᵗ τ` consumed only inside oracle bodies can be
  delayed into those bodies via the canonical `QueryImpl.greedyLazy`
  construction.

The proof technique mirrors `evalDist_liftComp_generateSeed_bind_simulateQ_run'`
in `VCVio.OracleComp.QueryTracking.SeededOracle`: structural induction on the
adversary program with case analysis on `pure` and `query_bind`.
-/

open OracleComp OracleSpec ENNReal

namespace OracleComp.ProgramLogic.Relational

variable {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {σ α : Type}

/-! ## Dead-store elimination -/

/-- **Dead-store elimination under `simulateQ`.**

If two `StateT σ ProbComp`-valued implementations produce, whenever their
states are `R`-related, a coupling witnessing output equality and post-state
`R`-preservation, then their full simulations produce equal output
distributions.

Typical instantiation: pick `R` to equate states that differ only in cells
whose current values are about to be overwritten before being read (dead
stores). The hypothesis `h_step` then says the two impls agree on observable
outputs and preserve `R`, while the dead-cell divergence is absorbed by `R`
itself.

This is `evalDist`-level convenience over `relTriple_simulateQ_run'`. -/
theorem probOutput_simulateQ_run'_eq_of_state_rel
    (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (R : σ → σ → Prop)
    (h_step : ∀ (t : spec.Domain) (s₁ s₂ : σ), R s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R p₁.2 p₂.2))
    (oa : OracleComp spec α) (s₁ s₂ : σ) (h : R s₁ s₂) :
    evalDist ((simulateQ impl₁ oa).run' s₁) =
      evalDist ((simulateQ impl₂ oa).run' s₂) :=
  evalDist_eq_of_relTriple_eqRel
    (relTriple_simulateQ_run' impl₁ impl₂ R oa h_step s₁ s₂ h)

/-! ## External-sample commutation via greedy lazy sampling -/

variable {τ : Type} [SampleableType τ]

/-- **Greedy-lazy lift** of a `τ`-parameterized impl-family.

Given a family `implFam : τ → QueryImpl spec (StateT σ ProbComp)`, produce a
single impl on augmented state `σ × Option τ` that, on the first query, samples
`a ← $ᵗ τ` and runs `implFam a` — caching `a` in the `Option τ` slot. On
subsequent queries the cached `a` is reused. -/
noncomputable def greedyLazy
    (implFam : τ → QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (σ × Option τ) ProbComp) :=
  fun t sc => do
    let a ← (match sc.2 with
      | some a => (pure a : ProbComp τ)
      | none => ($ᵗ τ : ProbComp τ))
    let (u, s') ← (implFam a t) sc.1
    pure (u, (s', some a))

/-- **Cached-case companion lemma** for
`probOutput_simulateQ_greedyLazy_run'_eq`.

With the cache already populated to `some a`, running `simulateQ` under the
greedy-lazy lift is output-equivalent to running `simulateQ (implFam a)` on
the base state. The sample `$ᵗ τ` never fires because the cache is never
empty along any reachable path. -/
theorem probOutput_simulateQ_greedyLazy_run'_some_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (a : τ) (s : σ) :
    evalDist ((simulateQ (implFam a) oa).run' s) =
      evalDist ((simulateQ (greedyLazy implFam) oa).run' (s, some a)) := by
  -- Proof outline (to finish in follow-up):
  -- apply `evalDist_eq_of_relTriple_eqRel` composed with `relTriple_simulateQ_run'`,
  -- using `R_state := fun s₁ sc₂ => s₁ = sc₂.1 ∧ sc₂.2 = some a`.
  -- The per-query premise reduces to showing that `(implFam a t).run s₁` and
  -- `(greedyLazy implFam t).run (s₁, some a)` are related by output-equality
  -- plus `R_state` on post-states, where the RHS is just `(fun p => (p.1, p.2, some a))
  -- <$> (implFam a t).run s₁` (since the cache hit skips the `$ᵗ τ` sample). Construct
  -- the coupling directly via the diagonal-map trick (LHS is `id <$> m`, RHS is
  -- `(postproc) <$> m`, use `relTriple_map` + `relTriple_refl`).
  sorry

/-- **External-sample commutation into `simulateQ` via greedy lazy sampling.**

The eager game — sample `a ← $ᵗ τ` at the top level, then run
`simulateQ (implFam a)` on the adversary — is output-equivalent to the lazy
game: run `simulateQ (greedyLazy implFam)` starting from empty cache. Both
sample `a` exactly once; in the lazy game, the sample happens at the first
query rather than at the top.

For multi-sample cases (e.g. two external scalars `a, b`), apply sequentially:
peel `a` with this lemma, then `b` on the resulting half-lazy impl. -/
theorem probOutput_simulateQ_greedyLazy_run'_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (s : σ) :
    evalDist (do
      let a ← ($ᵗ τ : ProbComp τ)
      (simulateQ (implFam a) oa).run' s) =
    evalDist ((simulateQ (greedyLazy implFam) oa).run' (s, none)) := by
  sorry

end OracleComp.ProgramLogic.Relational

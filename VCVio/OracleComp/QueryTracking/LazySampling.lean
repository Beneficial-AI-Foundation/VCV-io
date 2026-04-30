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
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp [simulateQ_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    -- Unfold `greedyLazy` at `some a` to a pure post-processing.
    have hg : (greedyLazy implFam t).run (s, some a) =
        (implFam a t).run s >>= fun p => (pure (p.1, p.2, some a) : ProbComp _) := by
      simp [greedyLazy, StateT.run]
    rw [hg, bind_assoc]
    simp only [pure_bind]
    -- Apply the inductive hypothesis pointwise.
    refine probOutput_bind_congr' _ y fun p => ?_
    have := ih p.1 p.2
    simp only [StateT.run'_eq, map_bind] at this
    exact congrFun (congrArg DFunLike.coe this) y

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
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s
    apply evalDist_ext
    intro y
    simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    -- Unfold `greedyLazy` at `none`: samples `a`, runs `implFam a`, caches.
    have hg : (greedyLazy implFam t).run (s, none) =
        (do let a ← ($ᵗ τ : ProbComp τ)
            let p ← (implFam a t).run s
            pure (p.1, p.2, some a)) := by
      simp [greedyLazy, StateT.run]
    rw [hg]
    -- Push bind associativity on both sides so the outer `$ᵗ τ` is shared.
    simp only [bind_assoc, pure_bind]
    -- Both sides now share the outer `$ᵗ τ >>= fun a => (implFam a t).run s >>= ...`;
    -- reduce to pointwise equality and close via the cached-case lemma.
    refine probOutput_bind_congr' _ y fun a => ?_
    refine probOutput_bind_congr' _ y fun p => ?_
    -- At this point, LHS continuation is `(simulateQ (implFam a) (k p.1)).run' p.2`
    -- and RHS continuation is `(simulateQ (greedyLazy implFam) (k p.1)).run' (p.2, some a)`
    -- (modulo the `Prod.fst <$> .run` / `.run'` conversion). Apply the cached lemma.
    have h_cached := probOutput_simulateQ_greedyLazy_run'_some_eq
      implFam (k p.1) a p.2
    simp only [StateT.run'_eq] at h_cached
    exact congrFun (congrArg DFunLike.coe h_cached) y

/-! ## Consume-site-lazy variant

`consumeLazy implFam hit` samples and caches the external `τ` only at queries
flagged by `hit : spec.Domain → Bool` — matching the pattern where the
external sample is consumed at specific oracle sites rather than on every
query. Requires the hypothesis that at non-hit queries, `implFam` is constant
in `τ` (its output distribution does not depend on the external value). -/

/-- **Consume-site-lazy lift.** Samples `a ← $ᵗ τ` only at queries where
`hit t = true` (and caches the first such sample). At `hit t = false`, uses
whatever is in the cache (or `default` if still empty) without observable
effect — under the hypothesis that `implFam` doesn't depend on `τ` at such
queries. -/
noncomputable def consumeLazy
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → Bool) [Inhabited τ] :
    QueryImpl spec (StateT (σ × Option τ) ProbComp) :=
  fun t sc => do
    if hit t then
      let a ← (match sc.2 with
        | some a => (pure a : ProbComp τ)
        | none => ($ᵗ τ : ProbComp τ))
      let (u, s') ← (implFam a t) sc.1
      pure (u, (s', some a))
    else
      let a : τ := sc.2.getD default
      let (u, s') ← (implFam a t) sc.1
      pure (u, (s', sc.2))

/-- **Cached-case companion lemma** for
`probOutput_simulateQ_consumeLazy_run'_eq`.

With the cache populated to `some a`, running `simulateQ` under the
consume-site-lazy lift is output-equivalent to running `simulateQ (implFam a)`
on the base state: at hit queries the cache is read (no sample); at non-hit
queries the cache is also read (via `getD`) and, because it happens to equal
`a`, the behavior matches `implFam a` regardless of `h_indep`. -/
theorem probOutput_simulateQ_consumeLazy_run'_some_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → Bool) [Inhabited τ]
    (oa : OracleComp spec α) (a : τ) (s : σ) :
    evalDist ((simulateQ (implFam a) oa).run' s) =
      evalDist ((simulateQ (consumeLazy implFam hit) oa).run' (s, some a)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp [simulateQ_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    -- Unfold `consumeLazy` at `some a` — same behavior whether `hit t` or not.
    have hg : (consumeLazy implFam hit t).run (s, some a) =
        (implFam a t).run s >>= fun p => (pure (p.1, p.2, some a) : ProbComp _) := by
      simp only [consumeLazy, StateT.run]
      split_ifs <;> simp [Option.getD]
    rw [hg, bind_assoc]
    simp only [pure_bind]
    refine probOutput_bind_congr' _ y fun p => ?_
    have := ih p.1 p.2
    simp only [StateT.run'_eq, map_bind] at this
    exact congrFun (congrArg DFunLike.coe this) y

/-- **External-sample consume-site commutation into `simulateQ`.**

If `implFam a` depends on `a` only at queries `t` with `hit t = true` (the
`h_indep` hypothesis), then sampling `a ← $ᵗ τ` at the top and running
`simulateQ (implFam a)` is output-equivalent to running
`simulateQ (consumeLazy implFam hit)` from the empty cache. The external
sample is effectively deferred to the first hit query. -/
theorem probOutput_simulateQ_consumeLazy_run'_eq
    (implFam : τ → QueryImpl spec (StateT σ ProbComp))
    (hit : spec.Domain → Bool) [Inhabited τ]
    (h_indep : ∀ (t : spec.Domain) (s : σ) (a₁ a₂ : τ),
      hit t = false → (implFam a₁ t).run s = (implFam a₂ t).run s)
    (oa : OracleComp spec α) (s : σ) :
    evalDist (do
      let a ← ($ᵗ τ : ProbComp τ)
      (simulateQ (implFam a) oa).run' s) =
    evalDist ((simulateQ (consumeLazy implFam hit) oa).run' (s, none)) := by
  revert s
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s
    apply evalDist_ext
    intro y
    simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t k ih =>
    intro s
    apply evalDist_ext
    intro y
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run'_eq, StateT.run_bind, map_bind]
    by_cases h : hit t = true
    · -- Hit query at empty cache: sample `a`, cache it, delegate to cached-case for the rest.
      have hg : (consumeLazy implFam hit t).run (s, none) =
          (do let a ← ($ᵗ τ : ProbComp τ)
              let p ← (implFam a t).run s
              pure (p.1, p.2, some a)) := by
        simp [consumeLazy, StateT.run, h]
      rw [hg]
      simp only [bind_assoc, pure_bind]
      refine probOutput_bind_congr' _ y fun a => ?_
      refine probOutput_bind_congr' _ y fun p => ?_
      have h_cached := probOutput_simulateQ_consumeLazy_run'_some_eq
        implFam hit (k p.1) a p.2
      simp only [StateT.run'_eq] at h_cached
      exact congrFun (congrArg DFunLike.coe h_cached) y
    · -- Non-hit query at empty cache: impl is `τ`-independent; commute the outer sample
      -- past this query via `probOutput_bind_bind_swap`, then apply IH.
      have h_false : hit t = false := by
        cases ht : hit t with
        | true => exact absurd ht h
        | false => rfl
      have hg : (consumeLazy implFam hit t).run (s, none) =
          (implFam (default : τ) t).run s >>= fun p =>
            (pure (p.1, p.2, (none : Option τ)) : ProbComp _) := by
        simp [consumeLazy, StateT.run, h_false, Option.getD]
      rw [hg]
      simp only [bind_assoc, pure_bind]
      -- Goal:
      --   Pr[= y | do a ← $F; p ← impl a t s; simulateQ (impl a) (k p.1) .run' p.2]
      --   = Pr[= y | do p ← impl default t s;
      --        simulateQ (consumeLazy impl hit) (k p.1) .run' (p.2, none)]
      have h_impl : ∀ a : τ, (implFam a t).run s = (implFam default t).run s :=
        fun a => h_indep t s a default h_false
      -- Step 1: replace `impl a t s` with `impl default t s` in LHS (under `a ← $F`).
      have eq1 : Pr[= y | do
            let a ← ($ᵗ τ : ProbComp τ)
            let p ← (implFam a t).run s
            Prod.fst <$> (simulateQ (implFam a) (k p.1)).run p.2] =
          Pr[= y | do
            let a ← ($ᵗ τ : ProbComp τ)
            let p ← (implFam default t).run s
            Prod.fst <$> (simulateQ (implFam a) (k p.1)).run p.2] := by
        refine probOutput_bind_congr' _ y fun a => ?_
        rw [h_impl a]
      rw [eq1]
      -- Step 2: swap `a ← $F` past `p ← impl default t s`.
      rw [probOutput_bind_bind_swap (mx := ($ᵗ τ : ProbComp τ))
          (my := (implFam default t).run s)
          (f := fun a p =>
            Prod.fst <$> (simulateQ (implFam a) (k p.1)).run p.2) (z := y)]
      -- Step 3: pointwise over `p`, apply IH at `p.2` (converting `.run'` ↔ `fst <$> .run`).
      refine probOutput_bind_congr' _ y fun p => ?_
      have h_ih := ih p.1 p.2
      simp only [StateT.run'_eq] at h_ih
      exact congrFun (congrArg DFunLike.coe h_ih) y

end OracleComp.ProgramLogic.Relational

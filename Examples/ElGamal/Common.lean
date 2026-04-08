/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Shared ElGamal-family helpers

Small distribution lemmas shared by the plain and hashed ElGamal examples.
-/


open OracleComp OracleSpec ENNReal

namespace ElGamalExamples

variable {A M : Type}
variable [AddGroup M] [SampleableType M]

/-- A fixed header plus a uniform additive mask hides which payload was chosen, even after an
arbitrary continuation from ciphertexts.

**One-time pad property with continuation.**
For any fixed `h : A`, any `m₁, m₂ : M`, and any function `cont : A × M → ProbComp β`,
the distributions `D(y ← U_M; cont(h, m₁ + y))` and `D(y ← U_M; cont(h, m₂ + y))` are
equal. The core reason is that `m + U_M` is uniformly distributed for every `m : M`
(shift invariance of the uniform distribution over a group), so the pair `(h, m₁ + y)` and
`(h, m₂ + y)` have the same distribution, and this is preserved by any post-processing `cont`. -/
lemma uniformMaskedCipher_bind_dist_indep {β : Type}
    (head : A) (m₁ m₂ : M) (cont : A × M → ProbComp β) :
    evalDist (do
      let y ← ($ᵗ M : ProbComp M)
      cont (head, m₁ + y)) =
    evalDist (do
      let y ← ($ᵗ M : ProbComp M)
      cont (head, m₂ + y)) := by
  -- Step 1: prove `hmask`: D(y ← U_M; (h, m₁ + y)) = D(y ← U_M; (h, m₂ + y)).
  -- Shift invariance: m₁ + U_M ≡ m₂ + U_M, so (h, m₁ + U_M) ≡ (h, m₂ + U_M).
  have hmask :
      evalDist (((fun y : M => (head, m₁ + y)) <$> ($ᵗ M : ProbComp M))) =
        evalDist (((fun y : M => (head, m₂ + y)) <$> ($ᵗ M : ProbComp M))) := by
    -- The proof term below passes two named arguments (`:=`) to `evalDist_map_eq_of_evalDist_eq`:
    --
    -- (1) h := evalDist_add_left_uniform_eq m₁ m₂
    --     Shift invariance: D(m₁ + U_M) = D(m₂ + U_M).
    --
    -- (2) f := fun z => (head, z)
    --     Pair each value with the fixed `head`.
    --
    -- `evalDist_map_eq_of_evalDist_eq` combines them: D(X) = D(Y) → D(f <$> X) = D(f <$> Y).
    -- Result: D(y ↦ (head, m₁ + y)) = D(y ↦ (head, m₂ + y)) when y ← U_M.
    --
    -- `simpa using` simplifies both the goal and the proof term's type, then matches them.
    simpa using
      evalDist_map_eq_of_evalDist_eq
        (h := evalDist_add_left_uniform_eq (α := M) m₁ m₂)
        (f := fun z : M => (head, z))
  -- Step 2: equal input distributions ⟹ equal output distributions after `cont`.
  -- Apply `congrArg`: if `X = Y` then `f(X) = f(Y)`.
  -- Here `f = fun p => p >>= fun c => evalDist (cont c)` marginalizes a PMF through `cont`
  -- (`>>=` on PMFs: `(p >>= g)(x) = ∑_c p(c) · g(c)(x)`; `evalDist` converts ProbComp → PMF).
  have h2 := congrArg (fun p => p >>= fun c => evalDist (cont c)) hmask
  -- h2 is an un-reduced application `f(X) = f(Y)` where:
  --   f = (fun p ↦ do c ← p; evalDist (cont c))   -- draw c from PMF p, return D(cont c)
  --   X = evalDist ((fun y ↦ (head, m₁+y)) <$> $ᵗM) -- PMF of (head, m₁ + U_M)
  --   Y = evalDist ((fun y ↦ (head, m₂+y)) <$> $ᵗM) -- PMF of (head, m₂ + U_M)
  --
  -- Goal: evalDist (do y ← $ᵗM; cont (head, m₁+y)) = evalDist (do y ← $ᵗM; cont (head, m₂+y))
  --
  -- After beta-reducing f(X), unfolding <$> as >>= ∘ pure, and applying `evalDist_bind`
  -- (which rewrites evalDist(mx >>= g) as evalDist(mx) >>= (evalDist ∘ g)),
  -- h2 and the goal become identical. `simpa` performs these rewrites.
  simpa [map_eq_bind_pure_comp, Function.comp, evalDist_bind, bind_assoc] using h2

end ElGamalExamples

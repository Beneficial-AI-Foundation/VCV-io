/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Security
import DoubleRatchet.CKA.MultiEpochGame
import DoubleRatchet.CKA.Figure3Game
import DoubleRatchet.Constructions.DDHCKA
import DoubleRatchet.Theorems.Reduction

/-!
# Theorem 3: DDH Security Implies CKA Security

Theorem 3 from Alwen-Coretti-Dodis (2020), Section 4.1.2, page 22.

**Statement**: If group G is (t,ε)-DDH-secure, then the DDH-based CKA scheme
is (t,Δ,ε)-secure for t ≈ t' and Δ = 1.

This file contains two layers of the theorem:

## Layer 1: Single-epoch warmup

A simple single-epoch reduction showing DDH hardness implies CKA security in
a one-shot game. The DDH adversary `ckaAdvToDDHAdv` receives `(g, aG, bG, cG)`
and forwards `(bG, cG)` directly to the CKA adversary:

- `ckaRealExp_eq_ddhExpReal` / `ckaRandExp_eq_ddhExpRand` — distribution equality
- `ddh_implies_cka_security` — concrete per-adversary bound
- `ddh_implies_cka_security_single_epoch` — epsilon-form warmup wrapper
- `ddh_implies_cka_security_delta` — restricted multi-epoch auxiliary form

## Layer 2: Figure 3 adaptive theorem surface

The paper-faithful statement over the full Figure 3 oracle game with adaptive
interaction, party-specific corruption, and bad-randomness oracles. The
reduction logic lives in `Theorems/Reduction.lean`; this file only states the
theorem:

- `figure3Advantage_le_ddhAdvantage` — helper two-game Figure 3 bound
- `figure3GuessAdvantage_le_ddhAdvantage` — paper-facing hidden-bit Figure 3 bound
- `ddh_implies_figure3_cka_security_two_game` — auxiliary two-game wrapper
- `ddh_implies_figure3_cka_security` — paper-faithful Theorem 3

For the asymptotic wrapper, see `Theorems/AsymptoticSecurity.lean`.

## Why `F`, `Module F G`, and `Function.Bijective (· • g)`?

The type-class `[Module F G]` says "F acts on G by scalar multiplication".
The hypothesis `hg : Function.Bijective (· • g : F → G)` encodes that
G ≅ F as an F-module via `a ↦ a • g` — i.e., G = ⟨g⟩ is cyclic of prime
order |F|. Needed for `ckaRandExp_eq_ddhExpRand`: the CKA random game samples
from G directly, while the DDH random game samples `c ← F` and computes
`c • g`. These are the same distribution iff `(· • g)` is bijective.
-/

set_option autoImplicit false

open OracleComp DiffieHellman

namespace CKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

/-- Given a CKA adversary, construct a DDH adversary with the same advantage.
The DDH adversary ignores `g` and `a • g` (the setup), and feeds
`(b • g, c • g)` = `(T, I_candidate)` to the CKA adversary. -/
def ckaAdvToDDHAdv (adversary : CKAAdversary G G) : DDHAdversary F G :=
  fun _g _aG bG cG => adversary bG cG

/-- The CKA real game with the DDH-CKA scheme produces the same distribution
as the DDH real game with the reduced adversary.

CKA real: sample `k ← F`, `x ← F`, adversary sees `(x • g, x • (k • g))`.
DDH real: sample `a ← F`, `b ← F`, adversary sees `(b • g, (a * b) • g)`.
These are identical (with `k = a`, `x = b` and using `smul_smul`). -/
lemma ckaRealExp_eq_ddhExpReal (g : G) (adversary : CKAAdversary G G) :
    ckaRealExp (SharedKey := F) (SenderState := G) (ReceiverState := F)
      (ddhCKA (F := F) g) adversary =
      ddhExpReal (F := F) g (ckaAdvToDDHAdv adversary) := by
  sorry

/-- The CKA random game with the DDH-CKA scheme produces the same distribution
as the DDH random game with the reduced adversary.

Requires `hg : Function.Bijective (· • g)` (i.e., g generates G): the CKA
random game samples uniformly from `G` via `$ᵗ G`, while the DDH random game
samples `c ← $ᵗ F` and computes `c • g`. These distributions coincide iff
`(· • g : F → G)` is bijective. -/
lemma ckaRandExp_eq_ddhExpRand (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (adversary : CKAAdversary G G) :
    ckaRandExp (SharedKey := F) (SenderState := G) (ReceiverState := F)
      (ddhCKA (F := F) g) adversary =
      ddhExpRand (F := F) g (ckaAdvToDDHAdv adversary) := by
  sorry

/-- **Theorem 3** (Alwen-Coretti-Dodis 2020), concrete per-adversary form:

For every CKA adversary `A`, its advantage against the DDH-CKA scheme is
bounded by the DDH advantage of the reduced adversary `ckaAdvToDDHAdv A`.

The hypothesis `hg` formalizes "G = ⟨g⟩ is cyclic of prime order |F|".
See the module docstring for why this is needed and how it relates to the
standard mathematical definition of a cyclic group. -/
theorem ddh_implies_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (adversary : CKAAdversary G G) :
    ckaDistAdvantage (ddhCKA (F := F) g) adversary ≤
      ddhDistAdvantage (F := F) g (ckaAdvToDDHAdv adversary) := by
  sorry

/-- **Theorem 3** (Alwen-Coretti-Dodis 2020), single-epoch epsilon form:

If every DDH adversary has advantage ≤ ε, then every single-epoch CKA
adversary has advantage ≤ ε. This follows from `ddh_implies_cka_security`
by instantiation.

**Note**: This targets `CKASecure` (single-epoch game), not the full
Figure 3 adaptive game. For the paper-faithful Figure 3 statement, see
`ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_cka_security_single_epoch (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    CKASecure (ddhCKA (F := F) g) ε := by
  sorry

/-- **Theorem 3** (restricted multi-epoch game, auxiliary, Δ=1):

If every DDH adversary has advantage ≤ ε, then the DDH-CKA scheme is
`CKASecureDelta` with Δ=1 in the restricted non-adaptive multi-epoch game.

**Note**: This targets `CKASecureDelta` from `MultiEpochGame.lean` — a
restricted non-adaptive game where the adversary commits upfront. This is
NOT the paper's full Figure 3 model. For the paper-faithful adaptive
statement, see `ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_cka_security_delta (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    CKASecureDelta (ddhCKA (F := F) g) 1 ε := by
  sorry

/-- **Theorem 3** (Figure 3 formulation with adaptive oracles):

Helper two-game bound for the concrete Figure 3 reduction. This is the
real-vs-random presentation used internally for reductions; the paper-facing
hidden-bit consequence is `figure3GuessAdvantage_le_ddhAdvantage`. -/
theorem figure3Advantage_le_ddhAdvantage (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ)
    (A : Figure3.Figure3Adversary F G G G F) :
    Figure3.figure3Advantage (ddhCKAWithCoins (F := F) g) tStar 1 A ≤
      ddhDistAdvantage (F := F) g (figure3AdvToDDHAdv (tStar, A)) := by
  sorry

/-- Paper-facing hidden-bit bound for the concrete Figure 3 reduction. -/
theorem figure3GuessAdvantage_le_ddhAdvantage (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ)
    (A : Figure3.Figure3Adversary F G G G F) :
    Figure3.figure3GuessAdvantage (ddhCKAWithCoins (F := F) g) tStar 1 A ≤
      ddhDistAdvantage (F := F) g (figure3AdvToDDHAdv (tStar, A)) := by
  simpa [Figure3.figure3GuessAdvantage_eq_figure3Advantage] using
    figure3Advantage_le_ddhAdvantage g hg tStar A

/-- Auxiliary Figure 3 wrapper in the derived two-game presentation.

This keeps the real-vs-random surface available for reduction-oriented proofs;
the primary paper-facing theorem is `ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_figure3_cka_security_two_game (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    Figure3.Figure3CKASecure (ddhCKAWithCoins (F := F) g) 1 ε := by
  intro tStar A
  exact le_trans (figure3Advantage_le_ddhAdvantage g hg tStar A) (hDDH _)

/-- **Theorem 3** (Figure 3 formulation with adaptive oracles):

If G is (t,ε)-DDH-secure, then the DDH-based CKA scheme is (t, Δ=1, ε)-secure
in the full Figure 3 game with adaptive oracle interaction, party-specific
corruption, and bad-randomness oracles.

This is the paper-faithful hidden-bit statement over the upgraded game model.
The concrete reduction is captured by `figure3GuessAdvantage_le_ddhAdvantage`,
and the theorem packages that pointwise bound into the Definition 13 surface. -/
theorem ddh_implies_figure3_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    Figure3.Figure3CKASecurePaper (ddhCKAWithCoins (F := F) g) 1 ε := by
  intro tStar A
  exact le_trans (figure3GuessAdvantage_le_ddhAdvantage g hg tStar A) (hDDH _)

end CKA

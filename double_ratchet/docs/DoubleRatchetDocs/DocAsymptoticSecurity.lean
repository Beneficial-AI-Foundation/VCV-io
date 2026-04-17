import VersoManual
import VersoBlueprint
import DoubleRatchet.Theorems.AsymptoticSecurity

open Verso.Genre Manual
open Informal

#doc (Manual) "Asymptotic Wrapper" =>
%%%
tag := "asymptotic_wrapper"
%%%

:::group "asymptotic_core"
Security-game wrappers that package the concrete theorem chain asymptotically.
:::

The paper states security with a runtime parameter `t`. The core concrete Lean
theorems instead quantify over adversaries directly and compare their
advantages pointwise. `Theorems/AsymptoticSecurity.lean` adds the standard
asymptotic wrapper on top of that concrete layer.

:::definition "asymptotic_games" (lean := "CKA.ddhSecurityGame, CKA.ckaSecurityGame, CKA.figure3CkaSecurityGame") (parent := "asymptotic_core")
Lean-only auxiliary definitions:

```
noncomputable def CKA.ddhSecurityGame (gFamily : ℕ → G) :
    SecurityGame (DDHAdversary F G)

noncomputable def CKA.ckaSecurityGame (gFamily : ℕ → G) :
    SecurityGame (CKAAdversary G G)

noncomputable def CKA.figure3CkaSecurityGame (gFamily : ℕ → G) :
    SecurityGame (ℕ × Figure3.Figure3Adversary F G G G F)
```

These are the `SecurityGame` wrappers used by the asymptotic library.
:::

This layer is explicitly secondary. It does not redefine the paper's semantics.
Instead, it lifts already established concrete bounds into the `secureAgainst`
framework used by VCV-io's asymptotic library.

:::definition "asymptotic_bridge" (lean := "CKA.ckaAdvantage_le_ddhAdvantage_ennreal, CKA.figure3GuessAdvantage_le_ddhAdvantage_ennreal") (parent := "asymptotic_core")
Lean-only bridge lemmas:

```
lemma CKA.ckaAdvantage_le_ddhAdvantage_ennreal
    (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (A : CKAAdversary G G) :
    ENNReal.ofReal (ckaDistAdvantage (ddhCKA (F := F) g) A) ≤
      ENNReal.ofReal (ddhDistAdvantage (F := F) g (ckaAdvToDDHAdv A))

lemma CKA.figure3GuessAdvantage_le_ddhAdvantage_ennreal
    (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ)
    (A : Figure3.Figure3Adversary F G G G F) :
    ENNReal.ofReal (Figure3.figure3GuessAdvantage
      (ddhCKAWithCoins (F := F) g) tStar 1 A) ≤
      ENNReal.ofReal (ddhDistAdvantage (F := F) g (figure3AdvToDDHAdv (tStar, A)))
```

These are the exact lifts from concrete `ℝ`-valued bounds to the
`ℝ≥0∞`-valued asymptotic API.
:::

:::theorem "figure3_asymptotic_theorem" (lean := "CKA.ddh_implies_figure3_cka_security_asymptotic") (parent := "asymptotic_core") (tags := "asymptotic, figure3, ddh") (effort := "medium") (priority := "medium")
Lean-only auxiliary theorem:

```
(ddhSecurityGame (F := F) gFamily).secureAgainst isPPT_DDH →
(figure3CkaSecurityGame (F := F) gFamily).secureAgainst isPPT_Fig3
```

Lean side, exact signature:

```
theorem CKA.ddh_implies_figure3_cka_security_asymptotic
    (gFamily : ℕ → G)
    (hg : ∀ sp, Function.Bijective (· • gFamily sp : F → G))
    (isPPT_Fig3 : (ℕ × Figure3.Figure3Adversary F G G G F) → Prop)
    (isPPT_DDH : DDHAdversary F G → Prop)
    (hreduce : ∀ AtStar, isPPT_Fig3 AtStar →
      isPPT_DDH (figure3AdvToDDHAdv AtStar))
    (hDDH : (ddhSecurityGame (F := F) gFamily).secureAgainst isPPT_DDH) :
    (figure3CkaSecurityGame (F := F) gFamily).secureAgainst isPPT_Fig3
```
:::

There is also a single-epoch asymptotic theorem,
`CKA.ddh_implies_cka_security_asymptotic`, but its proof is still admitted.
This matches the role of the whole asymptotic layer in the current project: it
is useful infrastructure, but not the authoritative paper-facing semantics.

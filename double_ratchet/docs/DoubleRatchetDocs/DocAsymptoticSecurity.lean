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
The asymptotic layer packages DDH, single-epoch CKA, and Figure 3 CKA as
instances of VCV-io's `SecurityGame` interface. Each game is indexed by a
security parameter and returns an `ENNReal` advantage.
:::

This layer is explicitly secondary. It does not redefine the paper's semantics.
Instead, it lifts already established concrete bounds into the `secureAgainst`
framework used by VCV-io's asymptotic library.

:::definition "asymptotic_bridge" (lean := "CKA.ckaAdvantage_le_ddhAdvantage_ennreal, CKA.figure3GuessAdvantage_le_ddhAdvantage_ennreal") (parent := "asymptotic_core")
The bridge lemmas convert concrete real-valued advantage inequalities into the
`ENNReal` inequalities required by the asymptotic API.
:::

:::theorem "figure3_asymptotic_theorem" (lean := "CKA.ddh_implies_figure3_cka_security_asymptotic") (parent := "asymptotic_core") (tags := "asymptotic, figure3, ddh") (effort := "medium") (priority := "medium")
The Figure 3 asymptotic theorem says that if DDH is secure against every PPT
DDH adversary, and the reduction preserves PPT, then the DDH-based CKA scheme
is secure against every PPT Figure 3 adversary.
:::

There is also a single-epoch asymptotic theorem,
`CKA.ddh_implies_cka_security_asymptotic`, but its proof is still admitted.
This matches the role of the whole asymptotic layer in the current project: it
is useful infrastructure, but not the authoritative paper-facing semantics.

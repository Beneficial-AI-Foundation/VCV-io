import VersoManual
import VersoBlueprint
import DoubleRatchet.Theorems.Theorem3
import DoubleRatchetDocs.SourceBlock

open Verso.Genre Manual
open Informal

#doc (Manual) "Theorem 3" =>
%%%
tag := "theorem3"
%%%

:::group "theorem3_core"
Warmup theorem surface, paper-facing Figure 3 theorem, and proof packaging.
:::

Theorem 3 is the main mathematical claim currently targeted by the project.
Informally, it says that if the underlying group is DDH-secure, then the
DDH-based CKA construction is secure with healing parameter `Delta = 1`.

The Lean development presents that result in layers, because the auxiliary
layers are useful when constructing the final proof.

:::definition "single_epoch_theorem_layer" (lean := "CKA.ckaAdvToDDHAdv, CKA.ckaRealExp_eq_ddhExpReal, CKA.ckaRandExp_eq_ddhExpRand, CKA.ddh_implies_cka_security, CKA.ddh_implies_cka_security_single_epoch") (parent := "theorem3_core")
The single-epoch layer is the warmup reduction. It already captures the core
DDH idea, but it only talks about one send and one distinguishing challenge,
not the adaptive Figure 3 game.
:::

This warmup layer is mathematically useful because it isolates the algebra of
the DDH embedding from the larger protocol interface. It is not the theorem the
paper ultimately states, so the site treats it as preparation rather than as
the endpoint.

:::definition "figure3_bound_layer" (lean := "CKA.figure3Advantage_le_ddhAdvantage, CKA.figure3GuessAdvantage_le_ddhAdvantage, CKA.ddh_implies_figure3_cka_security_two_game") (parent := "theorem3_core")
The next layer upgrades the argument to the full Figure 3 game. The helper
two-game bound is kept for reduction-oriented reasoning, and the paper-facing
hidden-bit bound is derived from it by the Figure 3 equivalence lemma.
:::

:::theorem "theorem3_paper" (lean := "CKA.ddh_implies_figure3_cka_security") (parent := "theorem3_core") (tags := "theorem3, figure3, ddh") (effort := "medium") (priority := "high")
`CKA.ddh_implies_figure3_cka_security` is the current paper-facing endpoint:
if every DDH adversary has advantage at most `epsilon`, then the DDH-based CKA
scheme is secure in the hidden-bit Figure 3 game with `Delta = 1`.
:::

:::proof "theorem3_paper"
Introduce the challenge epoch and the Figure 3 adversary, apply the concrete
paper-facing pointwise bound
`CKA.figure3GuessAdvantage_le_ddhAdvantage`, and finish with the assumed DDH
security bound for the reduced adversary.
:::

```source CKA.ddh_implies_figure3_cka_security
```

The important point is that the paper-facing theorem itself is already proved.
The admitted work sits underneath it, in the more detailed simulation and
distribution-equality lemmas that justify the pointwise reduction bound.

```tex "theorem3_paper"
\forall B,\; \mathrm{Adv}^{\mathrm{DDH}}(B) \le \varepsilon
\;\Longrightarrow\;
\forall t^\*, A,\;
\mathrm{Adv}^{\mathrm{CKA}}_{\mathrm{Figure3}, \Delta = 1}(A, t^\*) \le \varepsilon
```

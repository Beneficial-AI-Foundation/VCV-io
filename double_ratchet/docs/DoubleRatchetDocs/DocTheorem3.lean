import VersoManual
import VersoBlueprint
import DoubleRatchet.Theorems.Theorem3

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

# Single-Epoch Warmup Layer

The single-epoch warmup layer contains the reduction map `ckaAdvToDDHAdv`, the
distribution equalities `ckaRealExp_eq_ddhExpReal` and
`ckaRandExp_eq_ddhExpRand`, and the concrete bound
`ckaDistAdvantage (ddhCKA g) A ≤ ddhDistAdvantage g (ckaAdvToDDHAdv A)`.
It captures the DDH algebra but not the adaptive Figure 3 game.

Lean declarations:

```
def CKA.ckaAdvToDDHAdv : CKAAdversary G G → DDHAdversary F G

theorem CKA.ckaRealExp_eq_ddhExpReal ...

theorem CKA.ckaRandExp_eq_ddhExpRand ...

theorem CKA.ddh_implies_cka_security ...

theorem CKA.ddh_implies_cka_security_single_epoch ...
```

This warmup layer is mathematically useful because it isolates the algebra of
the DDH embedding from the larger protocol interface. It is not the theorem the
paper ultimately states, so the site treats it as preparation rather than as
the endpoint.

# Figure 3 Bound Layer

The Figure 3 layer upgrades the warmup statement to the exact bounds
`figure3Advantage ... ≤ ddhDistAdvantage ...` and
`figure3GuessAdvantage ... ≤ ddhDistAdvantage ...`,
and packages the helper two-game surface as
`ddh_implies_figure3_cka_security_two_game`.

Lean declarations:

```
theorem CKA.figure3Advantage_le_ddhAdvantage ...

theorem CKA.figure3GuessAdvantage_le_ddhAdvantage ...

theorem CKA.ddh_implies_figure3_cka_security_two_game ...
```

:::theorem "theorem3_paper" (lean := "CKA.ddh_implies_figure3_cka_security") (parent := "theorem3_core") (tags := "theorem3, figure3, ddh") (effort := "medium") (priority := "high")
The exact paper-facing endpoint is:
if
`∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε`,
then
`Figure3.Figure3CKASecurePaper (ddhCKAWithCoins (F := F) g) 1 ε`.

Paper side, normalized:

```
If G is (t, epsilon)-DDH-secure,
then the DDH-based CKA scheme is (t, Delta, epsilon)-secure
with Delta = 1.
```

Lean side, exact signature:

```
theorem CKA.ddh_implies_figure3_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    Figure3.Figure3CKASecurePaper (ddhCKAWithCoins (F := F) g) 1 ε
```

The important point is that the paper-facing theorem itself is already proved.
The admitted work sits underneath it, in the more detailed simulation and
distribution-equality lemmas that justify the pointwise reduction bound.
:::

```tex "theorem3_paper"
\forall B,\; \mathrm{Adv}^{\mathrm{DDH}}(B) \le \varepsilon
\;\Longrightarrow\;
\forall t^\*, A,\;
\mathrm{Adv}^{\mathrm{CKA}}_{\mathrm{Figure3}, \Delta = 1}(A, t^\*) \le \varepsilon
```

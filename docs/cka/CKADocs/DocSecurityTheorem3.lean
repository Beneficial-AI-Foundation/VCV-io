/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import CKADocs.SourceBlock
import Examples.CKA.FromDDH.Security

/-!
# Security and Theorem 3

Paper-to-code mapping for the hidden-bit game, DDH reduction, and final CKA
security theorem.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "Security Game and Theorem 3" =>
%%%
tag := "security_theorem3"
%%%

:::group "security_core"
The hidden-bit CKA game and the DDH reduction used for Theorem 3.
:::

The Lean file `Examples/CKA/FromDDH/Security.lean` proves a per-adversary
security theorem. Instead of quantifying over an abstract epsilon first, it
constructs the DDH adversary associated to a CKA adversary and bounds the CKA
advantage by that DDH advantage.

```
Proof pipeline:

CKA adversary A
  -> ddhCKA.securityReduction gp A
  -> DDH adversary against (g, g^a, g^b, g^c)
  -> real DDH branch simulates fixed-bit real CKA game
  -> random DDH branch simulates fixed-bit random CKA game
  -> branch difference bounds CKA hidden-bit advantage

Final shape:

CKAScheme.securityAdvantage (ddhCKA F G gen) A gp
  <= ddhGuessAdvantage gen (ddhCKA.securityReduction gp A)
```

:::definition "security_exp" (lean := "CKAScheme.securityExp, CKAScheme.securityAdvantage") (parent := "security_core")
Paper side, normalized hidden-bit game:

```
sample initial key material
initialize both parties
sample hidden bit b
run adversary A against the Figure 3 oracles
return whether A guessed b
```

Lean side:

```
def CKAScheme.securityExp
    [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CKAScheme.CKAAdversary St Rho I)
    (gp : CKAScheme.GameParams) : ProbComp Bool

noncomputable def CKAScheme.securityAdvantage
    [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CKAScheme.CKAAdversary St Rho I)
    (gp : CKAScheme.GameParams) : Real :=
  |(Pr[= true | securityExp cka adversary gp]).toReal - 1 / 2|
```

This is the paper's real-or-random hidden-bit advantage.
:::

:::definition "fixed_bit_decomposition" (lean := "CKAScheme.securityExpFixedBit, CKAScheme.securityExp_toReal_sub_half") (parent := "security_core")
The proof works with fixed hidden-bit branches.

Paper side:

```
b = false: challenge returns the real CKA key
b = true:  challenge returns an independent random key
```

Lean side:

```
def CKAScheme.securityExpFixedBit
    (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CKAScheme.CKAAdversary St Rho I)
    (b : Bool) (gp : CKAScheme.GameParams) : ProbComp Bool

lemma CKAScheme.securityExp_toReal_sub_half :
  Pr[securityExp wins] - 1/2 =
    (Pr[fixed true outputs true] - Pr[fixed false outputs true]) / 2
```

This decomposition is the bridge from the hidden-bit game to branch-by-branch
simulation lemmas.
:::

:::definition "security_reduction" (lean := "ddhCKA.securityReduction") (parent := "security_core")
The DDH reduction runs the CKA adversary against a challenger that embeds the
DDH tuple.

Paper side, Theorem 3 proof idea:

```
Given (g, g^a, g^b, g^c), build a CKA game for A.
Inject g^a at the send before the challenge.
Inject (g^b, g^c) at the challenge.
If c = ab, the challenge key is real.
If c is random, the challenge key is random.
```

Lean side:

```
noncomputable def ddhCKA.securityReduction
    (gp : CKAScheme.GameParams)
    (adversary : CKAScheme.CKAAdversary (F ⊕ G) G G) :
    DDHAdversary F G :=
  fun gen gA gB gT => do
    let s0 <- reductionInitState gp gen gA
    let (b', _) <-
      (simulateQ (reductionOracleImpl gp gen gA gB gT) adversary).run s0
    return !b'
```

The final negation aligns the CKA hidden-bit convention with the DDH guessing
convention used by the library.
:::

:::definition "placeholder_states" (parent := "security_core")
The reduction sometimes writes `.inl 0` when the DDH exponent is unknown.

Paper side:

```
The reduction knows group elements g^a and g^b, but not necessarily the
underlying scalars a and b.
```

Lean side:

```
state field : F ⊕ G
.inl 0      : scalar-shaped placeholder
```

This placeholder is not intended to represent a real secret known by the
reduction. The proof obligation is to show that the placeholder is either
unreachable at observable points or absorbed by the state relation used in the
simulation proof.
:::

:::definition "lazy_honest_bridge" (parent := "security_core")
The hard proof step compares the reduction game to a cache-aware honest game.

Paper side:

```
Real DDH branch:
  the embedded tuple behaves like honest CKA randomness.

Random DDH branch:
  the challenge key is independent of the honest transcript.
```

Lean side, proof architecture:

```
reductionOracleImpl
honestImpl_lazy_real
R_general
securityReduction_real
securityReduction_rand
```

The lazy honest game exposes the random scalars associated with the critical
send and challenge through caches, so the proof can couple them with the DDH
tuple branch-by-branch.
:::

:::theorem "theorem3_per_adversary" (lean := "ddhCKA.security") (parent := "security_core") (tags := "theorem3, ddh, cka") (effort := "large") (priority := "high")
Paper side, normalized Theorem 3:

```
If the group is DDH-secure, then DDH-CKA is CKA-secure with Delta_CKA = 1.
```

Lean side, per-adversary form:

```
theorem ddhCKA.security
    (gp : CKAScheme.GameParams)
    (hDelta : gp.deltaCKA = 1)
    (hg : Function.Bijective (fun x : F => x • gen))
    (adversary : CKAScheme.CKAAdversary (F ⊕ G) G G) :
    CKAScheme.securityAdvantage (ddhCKA F G gen) adversary gp <=
      ddhGuessAdvantage gen (ddhCKA.securityReduction gp adversary)
```

The usual epsilon statement follows by assuming every DDH adversary has
advantage at most epsilon and instantiating that assumption with the concrete
reduction `securityReduction gp adversary`.
:::

```source ddhCKA.security
```

/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import CKADocs.BlueprintTriptych
import CKADocs.Cryptocode
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

::::::::definition "security_exp" (lean := "CKAScheme.securityExp, CKAScheme.securityAdvantage") (parent := "security_core")
:::::::ckaItem "Hidden-bit CKA security game"
::::::ckaPaper
Paper side, normalized hidden-bit game:

:::::ckaGameGrid
::::ckaGameCell "Game G_CKA(lambda)" (kind := "game")
$`\lcka \sample \mathsf{Init\text{-}KeyGen}(1^\lambda)`

$`\stA \getsval \InitA(\lcka);\quad \stB \getsval \InitB(\lcka)`

$`t_A,t_B \getsval 0;\quad b \sample \{0,1\}`

$`b' \getsval \mathcal A(\lambda)`

$`\Return[b'=b]`
::::

::::ckaGameCell "Oracle O-Send-A" (kind := "oracle")
$`t_A {+}{+}`

$`(K_{t_A},\rho_{t_A},\stA) \sample \SendA(\stA)`

$`\Return(\rho_{t_A},K_{t_A})`
::::

::::ckaGameCell "Oracle O-Rec-B" (kind := "oracle")
$`t_B {+}{+}`

$`(K_{t_B},\stB) \getsval \RecB(\stB,\rho_{t_B})`

$`\Return\bot`
::::

::::ckaGameCell "Oracle O-Chall-A" (kind := "challenge")
$`t_A {+}{+}`

$`\req\;t_A=t^*`

$`(K_{t_A},\rho_{t_A},\stA) \sample \SendA(\stA)`

$`\mathsf{if}\;b=0\;\mathsf{then}\;\Return(\rho_{t_A},K_{t_A})`

$`\mathsf{else}\;K \sample \mathcal K;\;\Return(\rho_{t_A},K)`
::::

::::ckaGameCell "Oracle O-Corr-A" (kind := "corrupt")
$`\req\;(\allowcorr(A)\vee\finished(A))`

$`\Return\stA`
::::

::::ckaGameCell "Oracle O-Corr-B" (kind := "corrupt")
$`\req\;(\allowcorr(B)\vee\finished(B))`

$`\Return\stB`
::::

::::ckaGameCell "Security advantage" (kind := "security")
$`\mathsf{Win}_{\mathcal A} \getsval (b'=b)`

$`\mathsf{Adv}_{\mathsf{CKA}}(\mathcal A)
  = \left|\Pr[\mathsf{Win}_{\mathcal A}]-\frac12\right|`
::::
:::::
::::::

::::::ckaLean
Lean declarations: `CKAScheme.securityExp` and
`CKAScheme.securityAdvantage`.

The source panels below show the full experiment and advantage definition.

:::leanDetail
```leanSource CKAScheme.securityExp
```

```leanSource CKAScheme.securityAdvantage
```
:::
::::::

::::::ckaMeaning
`securityExp` is the executable Figure 3 wrapper: sample the setup, sample the
hidden bit, interpret the adversary with `ckaSecurityImpl`, and return whether
the adversary guessed the bit. `securityAdvantage` converts that success
probability into the paper's real-or-random advantage.
::::::
:::::::
::::::::

::::::definition "fixed_bit_decomposition" (lean := "CKAScheme.securityExpFixedBit, CKAScheme.securityExp_toReal_sub_half") (parent := "security_core")
:::::ckaItem "Fixed-bit decomposition"
::::ckaPaper
The proof works with fixed hidden-bit branches.

```
b = false: challenge returns the real CKA key
b = true:  challenge returns an independent random key
```
::::

::::ckaLean
Lean declarations: `CKAScheme.securityExpFixedBit` and
`CKAScheme.securityExp_toReal_sub_half`.

The definition is shown as source. The lemma is shown as an interactive
statement; its proof remains in the Lean file.

:::leanDetail
```leanSource CKAScheme.securityExpFixedBit
```

```leanSource CKAScheme.securityExp_toReal_sub_half
```
:::
::::

::::ckaMeaning
The sampled-bit game is reduced to two ordinary games with the challenge bit
fixed in advance. This is the algebraic bridge from the CKA hidden-bit
experiment to the two DDH branch simulations.
::::
:::::
::::::

::::::definition "security_reduction" (lean := "ddhCKA.securityReduction") (parent := "security_core")
:::::ckaItem "DDH adversary built from a CKA adversary"
::::ckaPaper
The DDH reduction runs the CKA adversary against a challenger that embeds the
DDH tuple.

```
Given (g, g^a, g^b, g^c), build a CKA game for A.
Inject g^a at the send before the challenge.
Inject (g^b, g^c) at the challenge.
If c = ab, the challenge key is real.
If c is random, the challenge key is random.
```
::::

::::ckaLean
Lean declaration: `ddhCKA.securityReduction`.

The full source is shown below. This reduction depends on private helper
definitions in the proof file, so it is displayed as exact source rather than
as a re-elaborated scratch declaration.

:::leanDetail
```leanSource ddhCKA.securityReduction
```
:::
::::

::::ckaMeaning
The reduction knows `g^a` and `g^b`, not necessarily `a` and `b`. At embedded
steps it can write scalar-shaped placeholders such as `.inl 0`; the simulation
proof shows those placeholders are dead at observable points or absorbed by
the state relation. The final `!b'` aligns the CKA hidden-bit convention with
the DDH guessing convention.
::::
:::::
::::::

::::::theorem "branch_simulations" (lean := "ddhCKA.securityReduction_real, ddhCKA.securityReduction_rand") (parent := "security_core") (tags := "theorem3, ddh, simulation") (effort := "large") (priority := "high")
:::::ckaItem "DDH branch simulations"
::::ckaPaper
The hard proof step compares the reduction game to a cache-aware honest game.

```
Real DDH branch:
  the embedded tuple behaves like honest CKA randomness.

Random DDH branch:
  the challenge key is independent of the honest transcript.
```
::::

::::ckaLean
Lean lemmas: `ddhCKA.securityReduction_real` and
`ddhCKA.securityReduction_rand`.

The statements below are rendered as Lean so their names and types can be
hovered. The proofs remain in the Lean file.

:::leanDetail
```leanSource ddhCKA.securityReduction_real
```

```leanSource ddhCKA.securityReduction_rand
```
:::
::::

::::ckaMeaning
The lazy honest game exposes the random scalars associated with the critical
send and challenge through caches, so the proof can couple them with the DDH
tuple branch-by-branch.
::::
:::::
::::::

::::::theorem "theorem3_per_adversary" (lean := "ddhCKA.security") (parent := "security_core") (tags := "theorem3, ddh, cka") (effort := "large") (priority := "high")
:::::ckaItem "Theorem 3, per-adversary form"
::::ckaPaper
Paper side, normalized Theorem 3:

```
If the group is DDH-secure, then DDH-CKA is CKA-secure with Delta_CKA = 1.
```
::::

::::ckaLean
Lean theorem: `ddhCKA.security`.

The theorem statement below is rendered as Lean. The proof remains in the Lean
file.

:::leanDetail
```leanSource ddhCKA.security
```
:::
::::

::::ckaMeaning
The usual epsilon statement follows by assuming every DDH adversary has
advantage at most epsilon and instantiating that assumption with the concrete
reduction `securityReduction gp adversary`.
::::
:::::
::::::

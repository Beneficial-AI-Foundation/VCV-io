/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import Examples.CKA.FromDDH.Correctness
import Examples.CKA.FromDDH.Security

/-!
# Correspondence Index

Compact paper-to-Lean mapping table for the CKA formalization.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "Correspondence Index" =>
%%%
tag := "correspondence_index"
%%%

:::group "index_core"
A compact lookup table for paper terms and Lean names.
:::

:::definition "notation_index" (parent := "index_core")
Notation map:

```
Paper                         Lean
---------------------------------------------------------------
g^x                           x • gen
h^x                           x • h
x <-$ S                       x <- $ᵗ S
Delta_CKA                     GameParams.deltaCKA
t*                            GameParams.tStar
P in {A, B}                   GameParams.challengedParty
t_A, t_B                      GameState.tA, GameState.tB
gamma_A, gamma_B              GameState.stA, GameState.stB
allow-corr                    CKAScheme.allowCorr
finished_A, finished_B        CKAScheme.finishedA, CKAScheme.finishedB
Pr[...]                       Pr[= value | computation]
```
:::

:::definition "oracle_index" (lean := "CKAScheme.ckaSecuritySpec, CKAScheme.ckaSecurityImpl") (parent := "index_core")
Oracle map:

```
Paper                         Lean domain alias / implementation
---------------------------------------------------------------
send-A                        OSendA / oracleSendA
receive-A                     ORecvA / oracleRecvA
send-B                        OSendB / oracleSendB
receive-B                     ORecvB / oracleRecvB
chall-A                       OChallA / oracleChallA
chall-B                       OChallB / oracleChallB
corr-A                        OCorruptA / oracleCorruptA
corr-B                        OCorruptB / oracleCorruptB
adversary private randomness  OUnif / oracleUnif
```

The fully qualified aliases live under `CKAScheme.ckaSecuritySpec`, for
example `CKAScheme.ckaSecuritySpec.OSendA`.
:::

:::definition "definition_index" (lean := "CKAScheme, CKAScheme.GameState, ddhCKA") (parent := "index_core")
Definition map:

```
Paper object                   Lean declaration
---------------------------------------------------------------
CKA scheme                     CKAScheme
Figure 3 game parameters       CKAScheme.GameParams
Figure 3 game state            CKAScheme.GameState
Figure 3 oracle spec           CKAScheme.ckaSecuritySpec
Figure 3 oracle semantics      CKAScheme.ckaSecurityImpl
CKA adversary                  CKAScheme.CKAAdversary
Correctness experiment         CKAScheme.correctnessExp
Security experiment            CKAScheme.securityExp
Fixed-bit branch               CKAScheme.securityExpFixedBit
CKA advantage                  CKAScheme.securityAdvantage
DDH-CKA construction           ddhCKA
DDH-CKA send                   ddhCKA.send
DDH-CKA receive                ddhCKA.recv
```
:::

:::definition "state_constructor_index" (parent := "index_core")
The two appearances of `.inl/.inr` must not be confused.

Oracle-spec sums:

```
.inl / .inr route into the left or right side of a binary sum of oracle specs.
Example: OCorruptB is the final right branch of ckaSecuritySpec.
```

DDH-CKA protocol state:

```
.inl x : F ⊕ G means scalar state x : F.
.inr h : F ⊕ G means group-element state h : G.
```

Same constructors, different sum types.
:::

:::theorem "theorem_index" (lean := "ddhCKA.correctness, ddhCKA.security") (parent := "index_core") (tags := "index, theorem3") (effort := "small") (priority := "medium")
Theorem map:

```
Paper object                         Lean theorem / lemma
--------------------------------------------------------------------
DDH-CKA correctness                  ddhCKA.correctness
hidden-bit branch decomposition      CKAScheme.securityExp_toReal_sub_half
real DDH branch simulation           ddhCKA.securityReduction_real
random DDH branch simulation         ddhCKA.securityReduction_rand
Theorem 3, per-adversary form        ddhCKA.security
```

The branch-simulation lemmas are the main bridge between the paper proof and
the final advantage inequality.
:::

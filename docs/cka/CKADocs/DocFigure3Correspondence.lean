/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import Examples.CKA.Defs

/-!
# Figure 3 Correspondence

Paper-to-code mapping for the CKA security oracle interface.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "Figure 3 Oracle Correspondence" =>
%%%
tag := "figure3_correspondence"
%%%

:::group "figure3_core"
The paper's Figure 3 oracles translated into nested oracle sums and named Lean
aliases.
:::

The current Lean game implements the Figure 3 oracle pattern as an oracle spec
whose domain is a nested sum. The nested `.inl` and `.inr` constructors come
from repeated binary sums of oracle specs.

The important point is that users should almost never reason with the raw
nested paths directly. The branch defines named aliases such as `OSendA` and
`OChallB` for the relevant paths.

```
Figure 3 translation map:

Paper oracle       Lean query alias                 Response type
send-A             ckaSecuritySpec.OSendA           Option (Rho × I)
receive-A          ckaSecuritySpec.ORecvA           Unit
send-B             ckaSecuritySpec.OSendB           Option (Rho × I)
receive-B          ckaSecuritySpec.ORecvB           Unit
chall-A            ckaSecuritySpec.OChallA          Option (Rho × I)
chall-B            ckaSecuritySpec.OChallB          Option (Rho × I)
corr-A             ckaSecuritySpec.OCorruptA        Option St
corr-B             ckaSecuritySpec.OCorruptB        Option St

Do not read .inl/.inr semantically here.
In this chapter they are only nested-sum routing tags.
```

:::definition "figure3_oracle_spec" (lean := "CKAScheme.ckaCorrectnessSpec, CKAScheme.ckaSecuritySpec") (parent := "figure3_core")
Paper side, current scope:

```
send-A
receive-A
send-B
receive-B
chall-A
chall-B
corr-A
corr-B
```

Lean side:

```
def CKAScheme.ckaCorrectnessSpec (Rho I : Type) :=
  unifSpec
  + (Unit ->o Option (Rho × I))
  + (Unit ->o Unit)
  + (Unit ->o Option (Rho × I))
  + (Unit ->o Unit)

def CKAScheme.ckaSecuritySpec (St Rho I : Type) :=
  CKAScheme.ckaCorrectnessSpec Rho I
  + (Unit ->o Option (Rho × I))
  + (Unit ->o Option (Rho × I))
  + (Unit ->o Option St)
  + (Unit ->o Option St)
```

The first summand is `unifSpec`, used for the adversary's internal
randomness. The remaining summands are the game oracles.
:::

:::definition "named_oracle_indices" (lean := "CKAScheme.ckaSecuritySpec.OSendA, CKAScheme.ckaSecuritySpec.ORecvA, CKAScheme.ckaSecuritySpec.OChallA, CKAScheme.ckaSecuritySpec.OCorruptA") (parent := "figure3_core")
The nested sum domain is given readable names.

Paper side:

```
send-A      receive-A      chall-A      corr-A
send-B      receive-B      chall-B      corr-B
```

Lean side:

```
CKAScheme.ckaSecuritySpec.OSendA
CKAScheme.ckaSecuritySpec.ORecvA
CKAScheme.ckaSecuritySpec.OSendB
CKAScheme.ckaSecuritySpec.ORecvB
CKAScheme.ckaSecuritySpec.OChallA
CKAScheme.ckaSecuritySpec.OChallB
CKAScheme.ckaSecuritySpec.OCorruptA
CKAScheme.ckaSecuritySpec.OCorruptB
```

These are marked with `@[match_pattern]`, so proofs can pattern-match against
the names while Lean unfolds them to the underlying `.inl/.inr` path.
:::

:::definition "inl_inr_oracle_paths" (lean := "CKAScheme.ckaSecuritySpec.OUnif, CKAScheme.ckaSecuritySpec.OSendA, CKAScheme.ckaSecuritySpec.OCorruptB") (parent := "figure3_core")
What `.inl` and `.inr` mean for oracle indices:

```
spec1 + spec2
```

has a domain that is a sum of query domains. A query in the left component is
tagged by `.inl`; a query in the right component is tagged by `.inr`.

Because `ckaSecuritySpec` is built by repeated binary sums, an oracle index is
a nested route through this binary tree.

Lean side, examples:

```
OUnif n =
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl n)))))))

OSendA =
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ())))))))

OCorruptB =
  .inr ()
```

So here `.inl` does not mean scalar state and `.inr` does not mean group
state. In this chapter they are only routing tags for a binary sum of oracle
interfaces.
:::

:::definition "send_receive_challenge_oracles" (lean := "CKAScheme.oracleSendA, CKAScheme.oracleRecvA, CKAScheme.oracleChallA, CKAScheme.oracleCorruptA") (parent := "figure3_core")
Each paper oracle is a concrete `QueryImpl` clause.

Paper side, normalized:

```
send-P:
  check it is P's turn
  t_P++
  run CKA-S
  store the outgoing message and sender key
  return (message, key)

receive-P:
  check it is P's turn
  t_P++
  deliver pending message
  run CKA-R
  check receiver key equals stored sender key

chall-P:
  check it is P's turn and t_P = t*
  run CKA-S
  return either real key or random key depending on hidden bit b

corr-P:
  return state only if allow-corr or finished_P holds
```

Lean side:

```
CKAScheme.oracleSendA
CKAScheme.oracleSendB
CKAScheme.oracleRecvA
CKAScheme.oracleRecvB
CKAScheme.oracleChallA
CKAScheme.oracleChallB
CKAScheme.oracleCorruptA
CKAScheme.oracleCorruptB
```

All of them target `StateT (GameState St I Rho) ProbComp`, so every oracle may
read and update the game state and may sample randomness when needed.
:::

:::definition "guards_as_options" (parent := "figure3_core")
The paper writes guards as `req ...`. In the Lean executable model, failed
guards are represented by `none` and no useful state change.

Paper side:

```
req condition
if condition fails, the oracle call does not go through
```

Lean side:

```
Option (Rho × I)
Option St
Unit
```

For send, challenge, and corruption oracles, `some value` means the call was
accepted and `none` means the guard failed. Receive returns `Unit`, but its
implementation still preserves the game state when the guard fails.
:::

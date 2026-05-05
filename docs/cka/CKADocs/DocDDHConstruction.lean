/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import CKADocs.SourceBlock
import Examples.CKA.FromDDH.Construction
import Examples.CKA.FromDDH.Common
import Examples.CKA.FromDDH.Correctness

/-!
# DDH Construction

Paper-to-code mapping for the DDH-based CKA construction.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "DDH-CKA Construction" =>
%%%
tag := "ddh_construction"
%%%

:::group "ddh_core"
The Section 4.1 construction translated into Mathlib scalar-action notation.
:::

The paper writes Diffie-Hellman multiplicatively, for example `g^x` and
`h^x`. The Lean formalization uses Mathlib's scalar action notation:

```
g^x      paper
x • gen  Lean

h^x      paper
x • h    Lean
```

Here `F` is the scalar field and `G` is the additive group/module carrying the
group action.

```
DDH-CKA translation map:

Paper object                    Lean object
scalar exponent x               x : F
group element h                 h : G
g^x                             x • gen
h^x                             x • h
local state gamma               F ⊕ G
scalar state                    .inl x
group-element state             .inr h
message T                       rho : G
epoch key I                     key : G
```

:::definition "ddh_state_sum" (lean := "ddhCKA") (parent := "ddh_core")
The DDH CKA state type is `F ⊕ G`.

Paper side:

```
The local state gamma alternates between:
  a secret scalar used to receive the next message
  a public/group element used to send the next message
```

Lean side:

```
St = F ⊕ G
```

Meaning of the constructors in this construction:

```
.inl x : F ⊕ G
  the party currently stores a scalar x : F.
  This is the receive-capable state.
  recv can compute x • rho.

.inr h : F ⊕ G
  the party currently stores a group element h : G.
  This is the send-capable state.
  send samples y and computes y • h.
```

This is different from the `.inl/.inr` in oracle indices. Here `.inl` and
`.inr` are the two cases of the protocol state type itself.
:::

:::definition "ddh_init" (lean := "ddhCKA") (parent := "ddh_core")
Paper side:

```
x0 <-$ F
h  := g^x0

init-A stores h
init-B stores x0
```

Lean side:

```
initKeyGen := do
  let x <- $ᵗ F
  return (x • gen, x)

initA := fun (h, _) => return .inr h
initB := fun (_, x) => return .inl x
```

So A begins with a group element and is ready to send first. B begins with the
matching scalar and is ready to receive.
:::

:::definition "ddh_send" (lean := "ddhCKA.send") (parent := "ddh_core")
Paper side:

```
Send(h):
  y <-$ F
  T := g^y
  I := h^y
  new state := y
  return (T, I)
```

Lean side:

```
def ddhCKA.send (gen : G) (st : F ⊕ G) :
    ProbComp (Option (G × G × (F ⊕ G))) :=
  match st with
  | .inr h => do
    let x <- $ᵗ F
    let key := x • h
    let msg := x • gen
    let st' : F ⊕ G := .inl x
    return some (key, msg, st')
  | .inl _ => return none
```

The generic `CKAScheme` send order is `(key, message, newState)`. The public
message is `x • gen`; the epoch key is `x • h`.
:::

:::definition "ddh_recv" (lean := "ddhCKA.recv") (parent := "ddh_core")
Paper side:

```
Receive(x, T):
  I := T^x
  new state := T
  return I
```

Lean side:

```
def ddhCKA.recv (st : F ⊕ G) (rho : G) :
    Option (G × (F ⊕ G)) :=
  match st with
  | .inl x =>
    let key := x • rho
    let st' : F ⊕ G := .inr rho
    some (key, st')
  | .inr _ => none
```

After receiving, the party stores the peer's public value `rho`, so it is
ready to send in the next round.
:::

:::theorem "ddh_correctness" (lean := "ddhCKA.correctness") (parent := "ddh_core") (tags := "correctness, ddh-cka") (effort := "medium") (priority := "medium")
The correctness proof shows that the sender and receiver derive the same group
element at every honest send/receive pair.

Paper side:

```
sender key   = y • (x • g)
receiver key = x • (y • g)

These are equal by commutativity of scalar multiplication.
```

Lean side:

```
theorem ddhCKA.correctness [DecidableEq G]
    (adv : CKAScheme.CKACorrectnessAdversary G G) :
    Pr[= true | CKAScheme.correctnessExp (ddhCKA F G gen) adv] = 1
```

The proof is driven by `reachableInv`, which records the four alternating
state shapes that can occur in an honest run.
:::

```source ddhCKA.correctness
```

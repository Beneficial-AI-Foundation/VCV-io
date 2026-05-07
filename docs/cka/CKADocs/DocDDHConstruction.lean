/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import CKADocs.BlueprintTriptych
import CKADocs.Cryptocode
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

The compact translation map is:

- scalar exponent `x` becomes `x : F`;
- group element `h` becomes `h : G`;
- `g^x` becomes `x • gen`;
- `h^x` becomes `x • h`;
- local state `γ` becomes `F ⊕ G`;
- message `T` and epoch key `I` both become values of `G` in this DDH
  instantiation.

::::::definition "ddh_cka" (lean := "ddhCKA") (parent := "ddh_core")
:::::ckaItem "DDH-CKA scheme"
::::ckaPaper
The Section 4.1 construction initializes the parties from one sampled scalar:

```
x0 <-$ F
h  := g^x0

init-A stores h
init-B stores x0
```

The local state alternates between a scalar used to receive the next message
and a group element used to send the next message.

:::ckaMsc
$$`\begin{array}{l|c|l}
\Alice & & \Bob \\ \hline
\cmnt{initialize} & & \cmnt{initialize} \\
\stA \getsval \chipF{\InitA(\lcka)} & & \stB \getsval \chipF{\InitB(\lcka)} \\
\cmnt{send from group state} & & \\
(\chipK{K_1},\rho_1,\stA) \sample \chipF{\SendA(\stA)} & \msgR{\rho_1} & \\
& & \cmnt{derive } \chipK{K_1} \\
& & (\chipK{K_1},\stB) \getsval \chipF{\RecB(\stB,\rho_1)} \\
& & \cmnt{send from group state} \\
& & (\chipK{K_2},\rho_2,\stB) \sample \chipF{\SendB(\stB)} \\
\cmnt{derive } \chipK{K_2} & \msgL{\rho_2} & \\
(\chipK{K_2},\stA) \getsval \chipF{\RecA(\stA,\rho_2)} & &
\end{array}`
:::
::::

::::ckaLean
Lean entry point: `ddhCKA`.

The source below is the authoritative `CKAScheme` value. It sets
`initKeyGen`, `initA`, `initB`, `sendA`, `sendB`, `recvA`, and `recvB` in one
place.

:::leanDetail
```leanSource ddhCKA
```
:::
::::

::::ckaMeaning
The sum type is protocol state, not oracle routing. `.inl x` means the party
currently stores a scalar `x : F` and is receive-capable. `.inr h` means the
party stores a group element `h : G` and is send-capable.

A begins ready to send because it stores `.inr h`; B begins ready to receive
because it stores `.inl x0`.
::::
:::::
::::::

::::::definition "ddh_send" (lean := "ddhCKA.send") (parent := "ddh_core")
:::::ckaItem "DDH send"
::::ckaPaper
Paper send step:

```
Send(h):
  y <-$ F
  T := g^y
  I := h^y
  new state := y
  return (T, I)
```
::::

::::ckaLean
Lean declaration: `ddhCKA.send`.

The generic `CKAScheme` send order is `(key, message, newState)`. The source
below shows the public message `x • gen`, the epoch key `x • h`, and the state
transition back to a scalar.

:::leanDetail
```leanSource ddhCKA.send
```
:::
::::

::::ckaMeaning
The send procedure only succeeds from a group-element state `.inr h`. It
samples a fresh scalar, returns the public DH message and derived epoch key,
and stores the sampled scalar so the next step can receive.
::::
:::::
::::::

::::::definition "ddh_recv" (lean := "ddhCKA.recv") (parent := "ddh_core")
:::::ckaItem "DDH receive"
::::ckaPaper
Paper receive step:

```
Receive(x, T):
  I := T^x
  new state := T
  return I
```
::::

::::ckaLean
Lean declaration: `ddhCKA.recv`.

After receiving, the party stores the peer's public value `rho`, so it is
ready to send in the next round. The source below shows the accepted scalar
state and the rejected group-state branch.

:::leanDetail
```leanSource ddhCKA.recv
```
:::
::::

::::ckaMeaning
The receive procedure only succeeds from a scalar state `.inl x`. It computes
the same DH shared group element as the sender and switches to `.inr rho`, so
the next local action can be a send.
::::
:::::
::::::

::::::theorem "ddh_correctness" (lean := "ddhCKA.correctness") (parent := "ddh_core") (tags := "correctness, ddh-cka") (effort := "medium") (priority := "medium")
:::::ckaItem "DDH-CKA correctness"
::::ckaPaper
The correctness proof shows that the sender and receiver derive the same group
element at every honest send/receive pair:

```
sender key   = y • (x • g)
receiver key = x • (y • g)

These are equal by commutativity of scalar multiplication.
```
::::

::::ckaLean
Lean theorem: `ddhCKA.correctness`.

The statement below is rendered as Lean so the names can be hovered. The proof
itself is left in the Lean file; it is driven by `reachableInv`, which records
the four alternating state shapes that can occur in an honest run.

:::leanDetail
```leanSource ddhCKA.correctness
```
:::
::::

::::ckaMeaning
The theorem quantifies over every correctness adversary that schedules honest
send and receive oracles. The probability is one because every reachable
receive-side key matches the pending sender key.
::::
:::::
::::::

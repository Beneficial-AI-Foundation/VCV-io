/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import CKADocs.SourceBlock
import Examples.CKA.Defs

/-!
# Introduction

Introductory chapter for the paper-to-code CKA documentation.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "Scope and Reading Strategy" =>
%%%
tag := "intro"
%%%

:::group "intro_core"
What this formalization is trying to mirror from the paper, and what it
intentionally leaves out.
:::

The current CKA development lives under `Examples/CKA`. It is not the older
standalone `double_ratchet` subproject. The Lean code uses VCV-io directly:
the adversary is syntax in `OracleComp`, the challenger is a `QueryImpl`, and
running the game means interpreting oracle syntax with `simulateQ`.

This documentation is organized as a face-to-face translation guide. Each
important item is presented in two parts:

```
Paper side:
  normalized mathematical or pseudocode form

Lean side:
  exact declaration, type, or code shape used in this branch
```

The paper side is intentionally normalized rather than copied. It records the
mathematical content needed to compare with the Lean declarations.

```
How to read the site:

Scope                 what the current branch models, and what it omits
VCV-io encoding       polynomial/free-monad/probability stack
Figure 3              paper oracles -> Lean oracle spec and QueryImpls
Game state            paper challenger variables -> Lean GameState fields
DDH construction      Section 4.1 protocol -> ddhCKA implementation
Security theorem      Theorem 3 proof idea -> reduction and final theorem
Index                 notation, aliases, and declaration lookup
```

{docH2 "Current Scope"}

The implementation covers a passive, alternating, static-challenge CKA game.
The target theorem is the DDH-based CKA security statement corresponding to
ACD19 Theorem 3, specialized to `Delta_CKA = 1`.

Paper side, normalized:

```
The adversary interacts with a Figure 3 challenger through send, receive,
challenge, and corruption oracles.

The challenge epoch t* and challenged party P are fixed by the experiment.
The challenger samples a hidden bit b and returns either the real CKA key or
an independent random key at the challenge.
```

Lean side, high-level:

```
structure CKAScheme (m : Type -> Type u) [Monad m] (IK St I Rho : Type)

abbrev CKAScheme.CKAAdversary (St Rho I : Type) :=
  OracleComp (CKAScheme.ckaSecuritySpec St Rho I) Bool
```

The Lean adversary is an adaptive oracle program whose only final result is a
Boolean guess.

The main type parameters and local abbreviations used throughout these docs are:

```
Name       Meaning in the Lean interface
IK         Initial shared key material.  `initKeyGen` samples `ik : IK`,
           then `initA` and `initB` initialize the two party states from it.
St         Per-party local protocol state.  The game stores one `St` for A
           and one `St` for B.
I          Epoch-key space.  Send and receive operations output keys `k : I`.
Rho        Protocol-message space, written `rho` / `ρ` in the protocol text.
           Send operations output messages `rho : Rho`; receive operations
           consume messages of the same type.
m          Ambient computation monad for the generic scheme interface.
ProbComp   VCV-io probabilistic computation monad, used by the DDH
           instantiation and by the security game.
gp         Game parameters: the fixed challenge epoch, healing delay, and
           challenged party.
tStar      Challenge epoch `t*` from the paper.
deltaCKA   Healing delay `Delta_CKA` from the paper.
```

{docH2 "Bad-randomness omission"}

The ACD19 Figure 3 game includes bad-randomness send oracles, usually written
as `send-P'(r)`. This branch intentionally omits them.

Paper side, full Figure 3:

```
send-P
send-P'(r)
receive-P
chall-P
corr-P
```

Lean side, current branch:

```
send-A, send-B
receive-A, receive-B
chall-A, chall-B
corr-A, corr-B
```

This is not proof debt for the current target. The omitted oracles are not
used in the post-quantum direction we want to build on next, and keeping them
out substantially reduces the proof surface.

:::definition "one_state_interface" (lean := "CKAScheme") (parent := "intro_core")
The older branch used separate sender and receiver state types. This branch
uses one state type `St`, and DDH-CKA later instantiates it with a sum type
`F ⊕ G`.

Paper side:

```
gamma is the local protocol state.
The protocol convention determines whether gamma is used by Send or Receive.
```

Lean side:

```
structure CKAScheme (m : Type -> Type u) [Monad m] (IK St I Rho : Type) where
  initKeyGen : m IK
  initA : IK -> m St
  initB : IK -> m St
  sendA : St -> m (Option (I × Rho × St))
  recvA : St -> Rho -> Option (I × St)
  sendB : St -> m (Option (I × Rho × St))
  recvB : St -> Rho -> Option (I × St)
```

Invalid phase/state combinations return `none`. This is the executable version
of a failed paper-side `req` guard.
:::

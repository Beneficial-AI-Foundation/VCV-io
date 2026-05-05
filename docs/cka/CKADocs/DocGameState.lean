/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual
import VersoBlueprint
import Examples.CKA.Defs

/-!
# Game State

Paper-to-code mapping for the state maintained by the Figure 3 challenger.
-/

open Verso.Genre Manual
open Informal

#doc (Manual) "Game State and Guards" =>
%%%
tag := "game_state"
%%%

:::group "state_core"
The state variables in the paper's game, and their concrete Lean fields.
:::

The challenger is stateful. It stores the two local protocol states, the last
undelivered message in each direction, the sender key paired with that message,
the hidden bit, the current communication phase, and the epoch counters.

```
GameState at a glance:

Field group          Lean fields                      Purpose
party states         stA, stB                         local protocol states
pending messages     rhoA, rhoB                       undelivered A->B / B->A messages
pending keys         keyA, keyB                       sender keys paired with messages
challenge bit        b                                real-vs-random hidden bit
correctness          correct                          accumulated receive-key checks
phase discipline     lastAction                       alternating communication guard
epoch counters       tA, tB                           per-party epoch counters
```

:::definition "game_params" (lean := "CKAScheme.GameParams, CKAScheme.CKAParty") (parent := "state_core")
Paper side:

```
t*             challenge epoch
Delta_CKA      healing delay
P              challenged party
```

Lean side:

```
structure CKAScheme.GameParams where
  tStar : Nat
  deltaCKA : Nat
  challengedParty : CKAScheme.CKAParty
```

The game fixes these parameters before the adversary runs.
:::

:::definition "game_state_fields" (lean := "CKAScheme.GameState") (parent := "state_core")
Paper side, normalized:

```
gamma_A, gamma_B
t_A, t_B
pending transcript values
hidden challenge bit b
correctness flag
```

Lean side:

```
structure CKAScheme.GameState (St I Rho : Type) where
  stA : St
  stB : St
  rhoA : Option Rho
  rhoB : Option Rho
  keyA : Option I
  keyB : Option I
  b : Bool
  correct : Bool
  lastAction : Option CKAScheme.CKAAction
  tA : Nat
  tB : Nat
```

`rhoA` is the latest undelivered message from A to B; `keyA` is the sender key
paired with it. The `B` fields are symmetric.
:::

:::definition "valid_step" (lean := "CKAScheme.validStep, CKAScheme.CKAAction") (parent := "state_core")
The current model enforces alternating communication.

Paper side, current scope:

```
A sends or challenges first.
Then B receives.
Then B sends or challenges.
Then A receives.
Repeat.
```

Lean side:

```
def CKAScheme.validStep
    (last : Option CKAScheme.CKAAction)
    (next : CKAScheme.CKAAction) : Bool
```

The accepted cycle is:

```
none
  -> sendA/challA
  -> recvB
  -> sendB/challB
  -> recvA
  -> sendA/challA
```
:::

:::definition "challenge_epoch" (lean := "CKAScheme.isChallengeEpoch, CKAScheme.isOtherSendBeforeChall") (parent := "state_core")
The challenge oracle is tied to the counter of the challenged party.

Paper side:

```
chall-P is accepted only at t_P = t*
the DDH reduction embeds the previous other-party send at t* - 1
```

Lean side:

```
def CKAScheme.isChallengeEpoch
    (gp : CKAScheme.GameParams)
    (state : CKAScheme.GameState St I Rho) : Bool :=
  state.tP gp.challengedParty == gp.tStar

def CKAScheme.isOtherSendBeforeChall
    (gp : CKAScheme.GameParams)
    (state : CKAScheme.GameState St I Rho) : Bool :=
  state.tP gp.challengedParty.other == gp.tStar - 1
```

The second predicate is reduction infrastructure: it identifies the send where
the DDH tuple is injected before the challenge.
:::

:::definition "corruption_guards" (lean := "CKAScheme.allowCorr, CKAScheme.finishedA, CKAScheme.finishedB") (parent := "state_core")
Paper side:

```
allow-corr       <=> max(t_A, t_B) <= t* - 2
finished_A       <=> t_A >= t* + Delta_CKA
finished_B       <=> t_B >= t* + Delta_CKA
```

Lean side:

```
def CKAScheme.allowCorr
    (gp : CKAScheme.GameParams)
    (state : CKAScheme.GameState St I Rho) : Bool :=
  (max state.tA state.tB) + 2 <= gp.tStar

abbrev CKAScheme.finishedA ...
abbrev CKAScheme.finishedB ...
```

The Lean inequality is the same guard written in `Nat` arithmetic.
:::

:::definition "initial_game_state" (lean := "CKAScheme.initGameState") (parent := "state_core")
Paper side:

```
initialize party states
clear pending messages and keys
set t_A = t_B = 0
sample or fix hidden bit b
```

Lean side:

```
def CKAScheme.initGameState (stA stB : St) (b : Bool) :
    CKAScheme.GameState St I Rho :=
  { stA, stB,
    rhoA := none, rhoB := none,
    keyA := none, keyB := none,
    b, correct := true, lastAction := none,
    tA := 0, tB := 0 }
```

`securityExp` samples `b`; `securityExpFixedBit` fixes it so the proof can
compare the real and random branches directly.
:::

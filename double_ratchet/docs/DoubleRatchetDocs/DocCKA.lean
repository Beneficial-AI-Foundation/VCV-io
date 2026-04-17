import VersoManual
import VersoBlueprint
import DoubleRatchet.CKA.Defs
import DoubleRatchet.CKA.SecurityGame
import DoubleRatchet.CKA.Security
import DoubleRatchet.CKA.MultiEpochGame

open Verso.Genre Manual
open Informal

#doc (Manual) "CKA Interface" =>
%%%
tag := "cka_interface"
%%%

:::group "cka_core"
CKA interface, warmup game, and auxiliary restricted game.
:::

The paper's starting point is a Continuous Key Agreement scheme. A CKA scheme
describes how two parties initialize shared state and then alternate sending
and receiving so that each epoch yields a fresh output key.

:::definition "cka_scheme_interface" (lean := "CKA.CKAScheme, CKA.CKASchemeWithCoins") (parent := "cka_core")
Paper side, normalized from Definition 12:

```
CKA = (CKA-Init-A, CKA-Init-B, CKA-S, CKA-R)

gamma_A <- CKA-Init-A(k)
gamma_B <- CKA-Init-B(k)
(gamma', T, I) <-$ CKA-S(gamma)
(gamma', I) <- CKA-R(gamma, T)
```

Lean side, exact declarations:

```
structure CKA.CKAScheme
    (SharedKey SenderState ReceiverState Msg Output : Type) where
  init : SharedKey → ProbComp (SenderState × ReceiverState)
  send : SenderState → ProbComp (ReceiverState × Msg × Output)
  recv : ReceiverState → Msg → ProbComp (SenderState × Output)

structure CKA.CKASchemeWithCoins
    (SharedKey SenderState ReceiverState Msg Output SendCoins : Type) where
  init : SharedKey → ProbComp (SenderState × ReceiverState)
  sendDet : SenderState → SendCoins → (ReceiverState × Msg × Output)
  recv : ReceiverState → Msg → ProbComp (SenderState × Output)
```

Lean merges the two initialization algorithms into one `init` returning both
initial states, and makes the sender/receiver alternation explicit in the
types.
:::

The paper writes a single abstract state `gamma`. Lean instead uses two state
types:

- `SenderState`: the state a party must hold when it is about to send;
- `ReceiverState`: the state a party must hold when it is about to receive.

This split makes the ping-pong discipline visible in the types. After a send,
the party moves into `ReceiverState`; after a receive, it moves back into
`SenderState`.

:::definition "single_epoch_warmup" (lean := "CKA.ckaRealExp, CKA.ckaRandExp, CKA.ckaDistAdvantage, CKA.CKASecure") (parent := "cka_core")
Lean-only auxiliary definitions:

```
def CKA.ckaRealExp
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (adversary : CKAAdversary Msg Output) : ProbComp Bool

def CKA.ckaRandExp
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (adversary : CKAAdversary Msg Output) : ProbComp Bool

noncomputable def CKA.ckaDistAdvantage
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (adversary : CKAAdversary Msg Output) : ℝ :=
  |(Pr[= true | ckaRealExp cka adversary]).toReal -
    (Pr[= true | ckaRandExp cka adversary]).toReal|

def CKA.CKASecure
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (ε : ℝ) : Prop :=
  ∀ adversary : CKAAdversary Msg Output,
    ckaDistAdvantage cka adversary ≤ ε
```

This is the single-epoch warmup layer used for the first DDH-to-CKA reduction.
It is auxiliary infrastructure, not the paper's full Definition 13 game.
:::

That warmup layer is useful because it isolates the simplest DDH embedding:
sample an initialization key, run one send, and ask whether the observed output
is real or random. It is the right abstraction for the first concrete reduction
step, but it omits the adaptive oracle interaction that matters for the paper.

:::definition "restricted_multi_epoch" (lean := "CKA.MultiEpochCKAAdversary, CKA.multiEpochAdvantage, CKA.CKASecureDelta") (parent := "cka_core")
Lean-only auxiliary definitions:

```
noncomputable def CKA.multiEpochAdvantage
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (delta : ℕ)
    (adversary : MultiEpochCKAAdversary Msg Output SenderState ReceiverState) : ℝ :=
  |(Pr[= true | multiEpochCKARealExp cka delta adversary]).toReal -
    (Pr[= true | multiEpochCKARandExp cka delta adversary]).toReal|

def CKA.CKASecureDelta
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (delta : ℕ) (ε : ℝ) : Prop :=
  ∀ adversary : MultiEpochCKAAdversary Msg Output SenderState ReceiverState,
    multiEpochAdvantage cka delta adversary ≤ ε
```

This is a restricted non-adaptive multi-epoch auxiliary layer. It is not the
canonical Figure 3 formalization.
:::

This distinction is important. The paper's Figure 3 game allows the adversary
to decide queries adaptively based on what it has already seen. The restricted
multi-epoch layer commits the adversary to the transcript shape in advance, so
it is documented as auxiliary throughout the site.

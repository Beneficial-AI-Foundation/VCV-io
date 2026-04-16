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
The main Lean interface is `CKA.CKAScheme`. Its explicit-coins refinement
`CKA.CKASchemeWithCoins` factors out the sender's randomness so that the
paper's bad-randomness oracle `send-P'(r)` can be modeled directly.
:::

The paper writes a single abstract state `gamma`. Lean instead uses two state
types:

- `SenderState`: the state a party must hold when it is about to send;
- `ReceiverState`: the state a party must hold when it is about to receive.

This split makes the ping-pong discipline visible in the types. After a send,
the party moves into `ReceiverState`; after a receive, it moves back into
`SenderState`.

:::definition "single_epoch_warmup" (lean := "CKA.ckaRealExp, CKA.ckaRandExp, CKA.ckaDistAdvantage, CKA.CKASecure") (parent := "cka_core")
`CKA/SecurityGame.lean` and `CKA/Security.lean` package a single-epoch
real-or-random game. This is auxiliary infrastructure for the warmup reduction,
not the paper's full Definition 13 game.
:::

That warmup layer is useful because it isolates the simplest DDH embedding:
sample an initialization key, run one send, and ask whether the observed output
is real or random. It is the right abstraction for the first concrete reduction
step, but it omits the adaptive oracle interaction that matters for the paper.

:::definition "restricted_multi_epoch" (lean := "CKA.MultiEpochCKAAdversary, CKA.multiEpochAdvantage, CKA.CKASecureDelta") (parent := "cka_core")
`CKA/MultiEpochGame.lean` adds a restricted multi-epoch game with a
non-adaptive adversary. It helps organize intermediate reasoning, but it is
not the canonical Figure 3 formalization.
:::

This distinction is important. The paper's Figure 3 game allows the adversary
to decide queries adaptively based on what it has already seen. The restricted
multi-epoch layer commits the adversary to the transcript shape in advance, so
it is documented as auxiliary throughout the site.

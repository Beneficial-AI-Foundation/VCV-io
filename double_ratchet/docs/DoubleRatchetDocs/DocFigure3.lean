import VersoManual
import VersoBlueprint
import DoubleRatchet.CKA.Figure3Game
import DoubleRatchetDocs.SourceBlock

open Verso.Genre Manual
open Informal

#doc (Manual) "Figure 3 Game" =>
%%%
tag := "figure3_game"
%%%

:::group "figure3_core"
Paper-faithful Figure 3 semantics and their Lean encoding.
:::

This is the central chapter of the current formalization. The file
`CKA/Figure3Game.lean` is the canonical Lean surface for Definition 13 and
Figure 3 from the paper.

:::definition "figure3_oracles" (lean := "CKA.Figure3.CKAQueryIdx, CKA.Figure3.ckaOracleSpec, CKA.Figure3.Figure3Adversary") (parent := "figure3_core")
The adversary interacts with explicit oracles for honest send, bad-randomness
send, receive, challenge, and corruption. In Lean these are the constructors of
`CKA.Figure3.CKAQueryIdx`, and a Figure 3 adversary is an `OracleComp` client
of that oracle spec together with private randomness.
:::

The game is stateful. The challenger tracks the local state of both parties,
their epoch counters, whose turn it is to act, whether a challenge has already
been used, and whether the post-challenge end condition has been reached.

:::definition "figure3_state" (lean := "CKA.Figure3.CKAGameState, CKA.Figure3.initialState, CKA.Figure3.GamePhase") (parent := "figure3_core")
`CKA.Figure3.CKAGameState` is the full challenger state. `GamePhase` enforces
the ping-pong order A send, B receive, B send, A receive, and so on. The
canonical starting configuration is packaged as `CKA.Figure3.initialState`.
:::

One subtle modeling choice is how the paper's `req` guards are represented. In
the paper, an invalid request simply does not go through. In Lean, each oracle
returns an `Option` result:

- `some ...` means the request was legal and the state was updated;
- `none` means the guard failed and the challenger state is unchanged.

This is not a semantic weakening. It is a faithful executable encoding of the
paper's rollback behavior.

:::definition "figure3_corruption" (lean := "CKA.Figure3.allowCorrFig3, CKA.Figure3.finishedParty, CKA.Figure3.corruptionPermittedFig3, CKA.Figure3.allowCorrPostIncrement") (parent := "figure3_core")
The corruption side conditions are modeled explicitly. `allowCorrFig3` encodes
the pre-window corruption rule, `finishedParty` encodes the post-healing rule,
and `allowCorrPostIncrement` captures the paper's special timing for
`send-P'(r)`.
:::

The paper-facing experiment is the hidden-bit game: the challenger samples a
bit `b`, the challenge oracle uses real or random output depending on `b`, and
the adversary wins by guessing `b`.

:::definition "figure3_paper_surface" (lean := "CKA.Figure3.figure3GuessExp, CKA.Figure3.figure3GuessAdvantage, CKA.Figure3.Figure3CKASecurePaper") (parent := "figure3_core")
The canonical public surface is the hidden-bit trio
`figure3GuessExp`, `figure3GuessAdvantage`, and `Figure3CKASecurePaper`.
These are the declarations that should be read as the Lean translation of the
paper's Figure 3 / Definition 13 security game.
:::

The file still exposes a two-game helper presentation because it is more
convenient for some reductions. The key bridge is fully proved.

:::theorem "figure3_hidden_bit_eq_two_game" (lean := "CKA.Figure3.figure3GuessAdvantage_eq_figure3Advantage") (parent := "figure3_core") (tags := "figure3, hidden-bit, equivalence") (effort := "medium") (priority := "high")
The paper-facing hidden-bit advantage coincides with the helper two-game
advantage. This lets the proof infrastructure use whichever presentation is
technically cleaner without changing the semantics of the theorem statement.
:::

:::proof "figure3_hidden_bit_eq_two_game"
Unfold the hidden-bit experiment, rewrite it as a uniform Boolean branch over
the real and random experiments, and invoke the generic Boolean equivalence
lemma from the probability library.
:::

```source CKA.Figure3.figure3GuessAdvantage_eq_figure3Advantage
```

```tex "figure3_paper_surface"
\mathrm{Adv}^{\mathrm{CKA}}_{\mathrm{ror},\Delta}(A)
\;=\;
\left| \Pr[A \text{ outputs } 1 \mid \mathrm{real}]
-
\Pr[A \text{ outputs } 1 \mid \mathrm{rand}] \right|
```

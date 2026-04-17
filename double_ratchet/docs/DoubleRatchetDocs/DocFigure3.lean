import VersoManual
import VersoBlueprint
import DoubleRatchet.CKA.Figure3Game

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
Paper side, normalized from Figure 3:

```
send-P
send-P'(r)
receive-P
chall-P
corr-P
```

Lean side, exact declarations:

```
inductive CKA.Figure3.CKAQueryIdx where
  | sendHonest : Party → CKAQueryIdx
  | sendBadRand : Party → SendCoins → CKAQueryIdx
  | receive : Party → CKAQueryIdx
  | challenge : Party → CKAQueryIdx
  | corrupt : Party → CKAQueryIdx

@[reducible] def CKA.Figure3.ckaOracleSpec :
    OracleSpec (CKAQueryIdx SendCoins)

abbrev CKA.Figure3.Figure3Adversary
    (SendCoins Msg Output SenderState ReceiverState : Type) :=
  OracleComp (Figure3OracleSpec SendCoins Msg Output SenderState ReceiverState) Bool
```

The five paper oracles become a typed oracle interface, and the adversary is an
`OracleComp` over that interface.
:::

The game is stateful. The challenger tracks the local state of both parties,
their epoch counters, whose turn it is to act, whether a challenge has already
been used, and whether the post-challenge end condition has been reached.

:::definition "figure3_state" (lean := "CKA.Figure3.CKAGameState, CKA.Figure3.initialState, CKA.Figure3.GamePhase") (parent := "figure3_core")
Lean side, exact declarations:

```
inductive CKA.Figure3.GamePhase where
  | awaitingSend : Party → GamePhase
  | awaitingReceive : Party → GamePhase

structure CKA.Figure3.CKAGameState (SenderState ReceiverState Msg : Type) where
  stateA : SenderState ⊕ ReceiverState
  stateB : SenderState ⊕ ReceiverState
  epochA : ℕ
  epochB : ℕ
  tStar : ℕ
  delta : ℕ
  challengeIsRandom : Bool
  phase : GamePhase
  pendingMsg : Option Msg
  challengeUsed : Bool
  corruptedPostChalA : Bool
  corruptedPostChalB : Bool

def CKA.Figure3.initialState
    (ss : SenderState) (rs : ReceiverState)
    (tStar delta : ℕ) (challengeIsRandom : Bool) :
    CKAGameState SenderState ReceiverState Msg
```

`GamePhase` enforces the ping-pong order, and `initialState` is the exact
challenger starting configuration.
:::

One subtle modeling choice is how the paper's `req` guards are represented. In
the paper, an invalid request simply does not go through. In Lean, each oracle
returns an `Option` result:

- `some ...` means the request was legal and the state was updated;
- `none` means the guard failed and the challenger state is unchanged.

This is not a semantic weakening. It is a faithful executable encoding of the
paper's rollback behavior.

:::definition "figure3_corruption" (lean := "CKA.Figure3.allowCorrFig3, CKA.Figure3.finishedParty, CKA.Figure3.corruptionPermittedFig3, CKA.Figure3.allowCorrPostIncrement") (parent := "figure3_core")
Paper side, normalized from Figure 3:

```
allow-corr_P  <=> max(t_A, t_B) <= t* - 2
finished_P    <=> t_P >= t* + Delta_CKA
```

Lean side, exact definitions:

```
def CKA.Figure3.allowCorrFig3
    (st : CKAGameState SenderState ReceiverState Msg) : Prop :=
  max st.epochA st.epochB + 2 ≤ st.tStar

def CKA.Figure3.finishedParty
    (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : Prop :=
  match p with
  | .A => st.epochA ≥ st.tStar + st.delta
  | .B => st.epochB ≥ st.tStar + st.delta

def CKA.Figure3.corruptionPermittedFig3
    (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : Prop :=
  allowCorrFig3 st ∨ finishedParty st p

def CKA.Figure3.allowCorrPostIncrement
    (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : Prop :=
  allowCorrFig3 (st.incEpoch p)
```

`allowCorrPostIncrement` is the executable version of the paper's
post-increment `req allow-corr` check for `send-P'(r)`.
:::

The paper-facing experiment is the hidden-bit game: the challenger samples a
bit `b`, the challenge oracle uses real or random output depending on `b`, and
the adversary wins by guessing `b`.

:::definition "figure3_paper_surface" (lean := "CKA.Figure3.figure3GuessExp, CKA.Figure3.figure3GuessAdvantage, CKA.Figure3.Figure3CKASecurePaper") (parent := "figure3_core")
Paper side, normalized from Figure 3 and Definition 13:

```
init(t*)
  ...
  b <-$ {0, 1}

chall-P
  ...
  if b = 0 then return real
  else return random

CKA is (t, Delta, epsilon)-secure if for all t-attackers A,
  Adv_CKA_ror,Delta(A) <= epsilon
```

Lean side, exact declarations:

```
def CKA.Figure3.figure3GuessExp
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (tStar delta : ℕ)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState) :
    ProbComp Bool := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let b' ← if b then
    figure3Exp cka tStar delta true adversary
  else
    figure3Exp cka tStar delta false adversary
  pure (b == b')

noncomputable def CKA.Figure3.figure3GuessAdvantage
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (tStar delta : ℕ)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState) : ℝ :=
  (figure3GuessExp cka tStar delta adversary).boolBiasAdvantage

def CKA.Figure3.Figure3CKASecurePaper
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (delta : ℕ) (ε : ℝ) : Prop :=
  ∀ (tStar : ℕ)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState),
    figure3GuessAdvantage cka tStar delta adversary ≤ ε
```

This is the canonical paper-facing hidden-bit surface.
:::

The file still exposes a two-game helper presentation because it is more
convenient for some reductions. The key bridge is fully proved.

:::theorem "figure3_hidden_bit_eq_two_game" (lean := "CKA.Figure3.figure3GuessAdvantage_eq_figure3Advantage") (parent := "figure3_core") (tags := "figure3, hidden-bit, equivalence") (effort := "medium") (priority := "high")
Paper side, normalized:

```
Adv_CKA_ror,Delta(A)
  = bias of the hidden-bit guessing game
  = |Pr[real] - Pr[rand]|
```

Lean side, exact signature:

```
lemma CKA.Figure3.figure3GuessAdvantage_eq_figure3Advantage
    [SampleableType SharedKey] [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState]
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (tStar delta : ℕ)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState) :
    figure3GuessAdvantage cka tStar delta adversary =
      figure3Advantage cka tStar delta adversary
```

This is the exact equivalence that lets the proof infrastructure switch between
the hidden-bit and two-game presentations without changing the theorem meaning.
:::

```tex "figure3_paper_surface"
\mathrm{Adv}^{\mathrm{CKA}}_{\mathrm{ror},\Delta}(A)
\;=\;
\left| \Pr[A \text{ outputs } 1 \mid \mathrm{real}]
-
\Pr[A \text{ outputs } 1 \mid \mathrm{rand}] \right|
```

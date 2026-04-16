import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal

#doc (Manual) "Crypto Primer" =>
%%%
tag := "crypto_primer"
%%%

:::group "primer_core"
Minimal background on game-based proofs, oracles, and reductions.
:::

This chapter gives the minimal cryptographic background needed to read the
formalization. It is intentionally short and operational: the goal is to make
the later Lean definitions legible without assuming prior exposure to protocol
security proofs.

:::definition "security_game" (parent := "primer_core")
A security game is an experiment between a challenger and an adversary. The
challenger samples hidden randomness, answers the adversary's queries according
to the game rules, and finally checks whether the adversary guessed some hidden
bit or distinguished two distributions.
:::

In this style of proof, security is not stated as "the protocol is secure" in
the abstract. Instead, one defines an explicit experiment and asks how well any
adversary can win it. The adversary's success probability is then compared
against a baseline such as random guessing.

:::definition "oracle_model" (parent := "primer_core")
An oracle is just a named interface that the adversary may query during the
game. In protocol proofs, the oracles usually stand for operations that the
adversary is allowed to trigger, such as sending, receiving, challenging, or
corrupting a party state.
:::

Lean packages this interaction in a monadic style. In VCV-io, an adversary is
an `OracleComp`: a computation that may ask oracle queries and eventually
return an output bit. This lets the same adversary description be interpreted
under different oracle implementations, which is exactly what a reduction proof
needs.

:::definition "advantage" (parent := "primer_core")
An advantage measures how much better the adversary does than the trivial
baseline. In a two-game setting, it is an absolute difference of
probabilities. In a hidden-bit setting, it is the bias above one half.
:::

The Double Ratchet formalization uses both views. The paper-facing Figure 3
surface uses a hidden-bit game, while some reduction steps are more convenient
in a real-vs-random two-game form. One of the important bridge lemmas shows
that these two presentations are equivalent for the Boolean games used here.

:::definition "reduction" (parent := "primer_core")
A reduction turns an adversary for one problem into an adversary for another
problem. If every adversary for the second problem has small advantage, then
the original adversary must also have small advantage.
:::

For Theorem 3, the reduction direction is:

- start with an adversary against the CKA security game;
- build from it an adversary against DDH;
- prove that the CKA advantage is bounded by the DDH advantage of the reduced
  adversary.

That is why later chapters focus so much on matching distributions exactly.
The main technical job is to show that the reduction's simulated game is the
same game the original adversary expected to see.

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

# Security Games

A security game is a randomized experiment `G` that returns a Boolean win bit.
For an adversary `A`, security is stated by bounding either `Pr[G(A) = true]`
against a baseline such as `1 / 2`, or the distance between two experiments
`|Pr[G_real(A) = true] - Pr[G_rand(A) = true]|`.

In this style of proof, security is not stated as "the protocol is secure" in
the abstract. Instead, one defines an explicit experiment and asks how well any
adversary can win it. The adversary's success probability is then compared
against a baseline such as random guessing.

# Oracle Model

An oracle model is a typed query/response interface `spec`. In Lean, an
adversary with oracle access is an `OracleComp spec Bool`: it may issue queries
from `spec`, receive the prescribed response type, and eventually return a bit.

Lean packages this interaction in a monadic style. In VCV-io, an adversary is
an `OracleComp`: a computation that may ask oracle queries and eventually
return an output bit. This lets the same adversary description be interpreted
under different oracle implementations, which is exactly what a reduction proof
needs.

# Advantage

An advantage is a concrete real number attached to an adversary. In the
two-game form it is `|Pr[real] - Pr[rand]|`; in the hidden-bit form it is
`|Pr[b' = b] - 1 / 2|`. The Double Ratchet development uses both forms and
proves they coincide for its Boolean-valued Figure 3 game.

The Double Ratchet formalization uses both views. The paper-facing Figure 3
surface uses a hidden-bit game, while some reduction steps are more convenient
in a real-vs-random two-game form. One of the important bridge lemmas shows
that these two presentations are equivalent for the Boolean games used here.

# Reduction

A reduction is a map `R` from adversaries for one game to adversaries for
another, together with a theorem of the form
`Adv_source(A) ≤ Adv_target(R A)`. This is the exact shape later used for the
DDH-to-CKA argument.

For Theorem 3, the reduction direction is:

- start with an adversary against the CKA security game;
- build from it an adversary against DDH;
- prove that the CKA advantage is bounded by the DDH advantage of the reduced
  adversary.

That is why later chapters focus so much on matching distributions exactly.
The main technical job is to show that the reduction's simulated game is the
same game the original adversary expected to see.

import VersoManual
import VersoBlueprint
import DoubleRatchet.Theorems.Reduction

open Verso.Genre Manual
open Informal

#doc (Manual) "Reduction Architecture" =>
%%%
tag := "reduction_architecture"
%%%

:::group "reduction_core"
Symbolic reduction state, concrete interpretation, and theorem scaffold.
:::

The file `Theorems/Reduction.lean` contains the executable heart of Theorem 3.
Its job is to build a DDH adversary that simulates the Figure 3 game for a CKA
adversary.

:::definition "reduction_symbolic_state" (lean := "CKA.Reduction.RedPub, CKA.Reduction.RedRecv, CKA.Reduction.RedState") (parent := "reduction_core")
The reduction stores symbolic state rather than pretending it knows every
secret. `RedPub` and `RedRecv` record whether the reduction knows a concrete
scalar or is instead carrying one of the unknown DDH challenge values.
`RedState` mirrors the control structure of the Figure 3 challenger.
:::

This symbolic layer is the right design for a cryptographic reduction. Around
the challenge window, the reduction must embed values coming from the external
DDH challenger. It can forward those group elements, but it does not know their
discrete logarithms. The symbolic state keeps that distinction explicit.

:::definition "reduction_interpretation" (lean := "CKA.Reduction.pubVal, CKA.Reduction.stateToConc, CKA.Reduction.redStateMatches") (parent := "reduction_core")
The reduction connects its symbolic state to the concrete CKA game through
interpretation functions. `pubVal` interprets symbolic public values,
`stateToConc` turns representable symbolic states into concrete party states,
and `redStateMatches` is the simulation relation used in the later proofs.
:::

The local invariant is also explicit.

:::definition "reduction_invariant" (lean := "CKA.Reduction.RedInv, CKA.Reduction.redQueryImpl_preservesRedInv") (parent := "reduction_core")
`RedInv` states that if corruption is legally allowed, then the symbolic party
state is representable as a concrete party state. The preservation theorem is
already stated but its proof is still admitted.
:::

That theorem is exactly where the paper's healing argument enters the formal
proof. Unknown exponents may appear only in a narrow window around the
challenge epoch, and the corruption guards are designed so that the adversary
cannot ask for those states while they still contain the hidden DDH secrets.

:::definition "reduction_adversary" (lean := "CKA.figure3AdvToDDHAdv") (parent := "reduction_core")
`CKA.figure3AdvToDDHAdv` is the actual reduction adversary. It receives a DDH
challenge `(g, aG, bG, cG)`, initializes the symbolic state, runs the Figure 3
adversary against the reduction's oracle implementation, and returns the final
guess bit to the DDH challenger.
:::

The rest of the file scaffolds the proof chain needed to show that this
simulation is correct.

:::theorem "reduction_distribution_chain" (lean := "CKA.reductionFigure3Impl_real_relTriple, CKA.reductionFigure3Sim_real_run'_relTriple, CKA.figure3Exp_real_eq_ddhExpReal, CKA.figure3Exp_rand_eq_ddhExpRand") (parent := "reduction_core") (tags := "reduction, distribution, simulation") (effort := "large") (priority := "high")
These theorems form the distribution-equality skeleton for the proof: first a
per-query relational correspondence, then a `simulateQ` lifting lemma, then the
final equalities between the Figure 3 experiments and the DDH experiments.
:::

At the moment these statements are in place but some proofs remain admitted.
That is deliberate: the scaffold fixes the exact proof architecture before the
proof-completion phase starts.

import VersoManual
import VersoBlueprint
import DoubleRatchet.Theorems.Theorem3

open Verso.Genre Manual
open Informal

#doc (Manual) "Project Scope" =>
%%%
tag := "project_scope"
%%%

:::group "scope_core"
Project status, current theorem boundary, and documentation conventions.
:::

This documentation covers the current `double_ratchet` subproject rather than
the full Double Ratchet paper. Today the implemented target is the CKA layer
and the DDH-based proof path that culminates in the paper-facing Figure 3 form
of Theorem 3.

The site is written for two readers at once:

- a Lean user who may know little cryptography and needs the proof pattern and
  game-based modeling explained carefully;
- a cryptographer who wants to verify that the Lean definitions really encode
  the paper's mathematics, not merely a loose approximation.

The current endpoint is the paper-facing theorem
`CKA.ddh_implies_figure3_cka_security`: if DDH is secure, then the DDH-based
CKA construction is secure in the full Figure 3 game with healing parameter
`Delta = 1`.

Several support layers exist around that endpoint:

- a single-epoch warmup game and reduction, useful for the first DDH to CKA
  argument;
- a restricted multi-epoch game, kept only as auxiliary infrastructure;
- an asymptotic wrapper that packages the concrete pointwise bounds into a
  standard negligible-advantage statement.

Definitions are intended to be complete and executable. Some theorem proofs are
still admitted with `sorry`, so this site distinguishes carefully between a
formalized statement and a completed proof.

That boundary matters for documentation quality. When a game definition is
described as canonical or paper-faithful here, that claim refers to the Lean
semantics already implemented in the corresponding definition. When a reduction
lemma or theorem is described as incomplete, that means the statement and proof
architecture are in place but the proof term still needs to be filled.

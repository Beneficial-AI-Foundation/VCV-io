import VersoManual
import VersoBlueprint
import DoubleRatchet.Constructions.DDHCKA

open Verso.Genre Manual
open Informal

#doc (Manual) "DDH-Based CKA" =>
%%%
tag := "ddh_cka"
%%%

:::group "ddhcka_core"
The concrete CKA construction used in Theorem 3.
:::

The paper's Section 4.1.2 instantiates the abstract CKA interface with a
Diffie-Hellman construction. This is the concrete scheme that later appears in
the Figure 3 reduction.

:::definition "ddh_cka_construction" (lean := "CKA.ddhCKA, CKA.ddhCKAWithCoins") (parent := "ddhcka_core")
`CKA.ddhCKA` is the DDH-based CKA scheme. `CKA.ddhCKAWithCoins` exposes the
same construction with explicit sender coins so that Figure 3 can model the
bad-randomness oracle directly.
:::

The Lean code uses additive notation, following Mathlib and VCV-io:

- the paper's `g^a` is written `a • g`;
- the paper's shared secret `g^{ab}` becomes `(a * b) • g`.

This choice is notation only. The mathematics is the same Diffie-Hellman
algebra.

The roles of the state types are especially transparent for this scheme:

- `SharedKey = F` is the initial scalar `x0`;
- `SenderState = G` stores the peer's public key;
- `ReceiverState = F` stores the party's own secret scalar;
- `Msg = G` is the transmitted DH share;
- `Output = G` is the agreed group element.

Correctness comes from the same algebra the paper uses: both parties compute
the same group element because scalar multiplication satisfies `smul_smul`.

:::definition "cyclic_group_interface" (parent := "ddhcka_core")
The construction is parameterized abstractly over a scalar field `F`, a group
`G`, and a generator `g : G`. The later theorem statements also assume
`Function.Bijective (fun a => a • g)`, which is the formal way this
development expresses that `g` generates a cyclic prime-order group.
:::

This abstraction comes from VCV-io's DDH library. It is slightly more general
than writing everything directly in `ZMod p`, and it keeps the scalar type and
group-element type separate. That matches many real cryptographic settings,
such as elliptic-curve groups where scalars and points have different concrete
representations.

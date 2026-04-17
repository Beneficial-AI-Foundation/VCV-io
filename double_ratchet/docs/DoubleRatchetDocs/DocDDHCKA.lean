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
Paper side, normalized from Section 4.1.2:

```
k = (h, x0) with h = g^x0

CKA-Init-A(k) returns h
CKA-Init-B(k) returns x0

CKA-S(h):
  x <-$ F
  T <- g^x
  I <- h^x
  gamma' <- x
  return (gamma', T, I)

CKA-R(x, T):
  I <- T^x
  gamma' <- T
  return (gamma', I)
```

Lean side, exact definitions:

```
def CKA.ddhCKA (g : G) : CKAScheme F G F G G where
  init k := pure (k • g, k)
  send h := do
    let x ← $ᵗ F
    pure (x, x • g, x • h)
  recv x msg := pure (msg, x • msg)

def CKA.ddhCKAWithCoins (g : G) : CKASchemeWithCoins F G F G G F where
  init k := pure (k • g, k)
  sendDet h x := (x, x • g, x • h)
  recv x msg := pure (msg, x • msg)
```

`ddhCKAWithCoins` is the explicit-coins version needed for the Figure 3
bad-randomness oracle.
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
Paper side:

```
G = <g>
```

Lean side:

```
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

hg : Function.Bijective (fun a => a • g : F → G)
```

This is the VCV-io / Mathlib expression of the paper's cyclic-group assumption.
:::

This abstraction comes from VCV-io's DDH library. It is slightly more general
than writing everything directly in `ZMod p`, and it keeps the scalar type and
group-element type separate. That matches many real cryptographic settings,
such as elliptic-curve groups where scalars and points have different concrete
representations.

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
Lean side, exact declarations:

```
inductive CKA.Reduction.RedPub (F : Type) where
  | known : F → RedPub F
  | aPub
  | bPub

inductive CKA.Reduction.RedRecv (F : Type) where
  | known : F → RedRecv F
  | aSec
  | bSec

structure CKA.Reduction.RedState (F : Type) where
  stateA : RedPub F ⊕ RedRecv F
  stateB : RedPub F ⊕ RedRecv F
  epochA : ℕ
  epochB : ℕ
  tStar : ℕ
  delta : ℕ
  phase : GamePhase
  pendingMsg : Option (RedPub F)
  challengeUsed : Bool
  corruptedPostChalA : Bool
  corruptedPostChalB : Bool
```

The reduction keeps symbolic unknowns instead of pretending it knows the DDH
challenge exponents.
:::

This symbolic layer is the right design for a cryptographic reduction. Around
the challenge window, the reduction must embed values coming from the external
DDH challenger. It can forward those group elements, but it does not know their
discrete logarithms. The symbolic state keeps that distinction explicit.

:::definition "reduction_interpretation" (lean := "CKA.Reduction.pubVal, CKA.Reduction.stateToConc, CKA.Reduction.redStateMatches") (parent := "reduction_core")
Lean side, exact declarations:

```
def CKA.Reduction.pubVal (g aG bG : G) : RedPub F → G

def CKA.Reduction.stateToConc
    (g aG bG : G) : RedPub F ⊕ RedRecv F → Option (G ⊕ F)

def CKA.Reduction.redStateMatches
    (g : G) (a b : F) (rst : RedState F)
    (cst : Figure3.CKAGameState G F G) : Prop
```

`redStateMatches` is the simulation relation connecting the symbolic reduction
state to the concrete Figure 3 challenger.
:::

The local invariant is also explicit.

:::definition "reduction_invariant" (lean := "CKA.Reduction.RedInv, CKA.Reduction.redQueryImpl_preservesRedInv") (parent := "reduction_core")
Lean side, exact definitions and theorem signature:

```
def CKA.Reduction.RedInv (g aG bG : G) (st : RedState F) : Prop :=
  ∀ p, st.corruptionPermitted p →
    (stateToConc (F := F) g aG bG (st.redStateOf p)).isSome

theorem CKA.Reduction.redQueryImpl_preservesRedInv
    (g aG bG cG : G) :
    QueryImpl.PreservesInv (redQueryImpl (F := F) g aG bG cG)
      (RedInv (F := F) g aG bG)
```

This invariant is the Lean form of the paper's healing argument: legal
corruption queries never expose a symbolic secret that the reduction cannot
interpret concretely.
:::

That theorem is exactly where the paper's healing argument enters the formal
proof. Unknown exponents may appear only in a narrow window around the
challenge epoch, and the corruption guards are designed so that the adversary
cannot ask for those states while they still contain the hidden DDH secrets.

:::definition "reduction_adversary" (lean := "CKA.figure3AdvToDDHAdv") (parent := "reduction_core")
Paper side, normalized from the proof of Theorem 3:

```
embed g^a at epoch t* - 1
embed g^b and g^c at epoch t*
use fresh randomness again after the challenge window
```

Lean side, exact definition:

```
def CKA.figure3AdvToDDHAdv
    (AtStar : ℕ × Figure3.Figure3Adversary F G G G F) :
    DDHAdversary F G :=
  fun g aG bG cG => do
    let initSt ←
      if AtStar.1 = 1 then
        pure (Reduction.initRedStateEmbedInit (F := F))
      else do
        let k ← $ᵗ F
        pure (Reduction.initRedState k AtStar.1)
    let guess ← (simulateQ (Reduction.reductionFigure3Impl (F := F) g aG bG cG)
      AtStar.2).run' initSt
    pure guess
```

This is the executable DDH adversary used in the reduction.
:::

The rest of the file scaffolds the proof chain needed to show that this
simulation is correct.

:::theorem "reduction_distribution_chain" (lean := "CKA.reductionFigure3Impl_real_relTriple, CKA.reductionFigure3Sim_real_run'_relTriple, CKA.figure3Exp_real_eq_ddhExpReal, CKA.figure3Exp_rand_eq_ddhExpRand") (parent := "reduction_core") (tags := "reduction, distribution, simulation") (effort := "large") (priority := "high")
Lean side, exact theorem signatures:

```
theorem CKA.reductionFigure3Impl_real_relTriple ...

theorem CKA.reductionFigure3Sim_real_run'_relTriple ...

theorem CKA.figure3Exp_real_eq_ddhExpReal
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ) (A : Figure3.Figure3Adversary F G G G F) :
    evalDist (Figure3.figure3Exp (ddhCKAWithCoins (F := F) g) tStar 1 false A) =
      evalDist (ddhExpReal (F := F) g (figure3AdvToDDHAdv (tStar, A)))

theorem CKA.figure3Exp_rand_eq_ddhExpRand
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ) (A : Figure3.Figure3Adversary F G G G F) :
    evalDist (Figure3.figure3Exp (ddhCKAWithCoins (F := F) g) tStar 1 true A) =
      evalDist (ddhExpRand (F := F) g (figure3AdvToDDHAdv (tStar, A)))
```

This is the precise simulation chain that turns the executable reduction into
the Figure 3 to DDH distribution equalities.
:::

At the moment these statements are in place but some proofs remain admitted.
That is deliberate: the scaffold fixes the exact proof architecture before the
proof-completion phase starts.

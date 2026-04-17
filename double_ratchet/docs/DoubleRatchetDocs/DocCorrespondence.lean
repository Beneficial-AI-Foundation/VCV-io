import VersoManual
import VersoBlueprint
import DoubleRatchet.CKA.Figure3Game
import DoubleRatchet.Constructions.DDHCKA
import DoubleRatchet.Theorems.Theorem3

open Verso.Genre Manual
open Informal

#doc (Manual) "Paper-to-Lean Correspondence" =>
%%%
tag := "paper_to_lean"
%%%

:::group "correspondence_core"
How the paper's notation and definitions map to the Lean formalization.
:::

This chapter refines the standalone correspondence note in `doc/`. The goal is
not only to list names, but to explain why the Lean declarations are the right
translation of the paper's mathematics.

For the three paper items that matter most, the chapter gives a normalized
paper-side statement together with the exact Lean declaration that implements
it. The paper-side blocks are not raw PDF quotations: they preserve the
mathematical content while normalizing notation and omitting prose around the
definitions.

:::definition "notation_map" (parent := "correspondence_core")
The paper's multiplicative Diffie-Hellman notation is translated into Mathlib's
additive scalar-action notation. Concretely:

```
g^a                      ↦  a • g
x <-$ S                  ↦  x ← $ᵗ S
Adv_CKA_ror,Delta(A)     ↦  CKA.Figure3.figure3GuessAdvantage ...
Adv_DDH(B)               ↦  ddhDistAdvantage ...
```
:::

:::definition "definition12_map" (lean := "CKA.CKAScheme") (parent := "correspondence_core")
Definition 12 of the paper becomes the Lean structure `CKA.CKAScheme`. The
paper's initialization, send, and receive algorithms are represented as the
fields `init`, `send`, and `recv`.

Paper side, normalized:

```
CKA = (CKA-Init-A, CKA-Init-B, CKA-S, CKA-R)

gamma_A <- CKA-Init-A(k)
gamma_B <- CKA-Init-B(k)
(gamma', T, I) <-$ CKA-S(gamma)
(gamma', I) <- CKA-R(gamma, T)
```

Lean side, exact declaration:

```
structure CKA.CKAScheme
    (SharedKey SenderState ReceiverState Msg Output : Type) where
  init : SharedKey → ProbComp (SenderState × ReceiverState)
  send : SenderState → ProbComp (ReceiverState × Msg × Output)
  recv : ReceiverState → Msg → ProbComp (SenderState × Output)
```

The only intentional change in the Lean surface is structural: the paper has
separate `CKA-Init-A` and `CKA-Init-B`, while Lean packages them into one
`init` that returns both initial states. Lean also makes the sender/receiver
state alternation explicit by splitting the state type into `SenderState` and
`ReceiverState`.
:::

:::definition "definition13_map" (lean := "CKA.Figure3.Figure3CKASecurePaper, CKA.Figure3.figure3GuessAdvantage") (parent := "correspondence_core")
Definition 13 is represented canonically by `Figure3CKASecurePaper` together
with `figure3GuessAdvantage`. These declarations expose the hidden-bit Figure 3
game rather than only a derived two-game presentation.

Paper side, normalized:

```
init(t*)
  k <-$ K
  gamma_A <- CKA-Init-A(k)
  gamma_B <- CKA-Init-B(k)
  t_A, t_B <- 0
  b <-$ {0, 1}

chall-P
  t_P++
  req t_P = t*
  (gamma', T_tP, I_tP) <-$ CKA-S(gamma)
  if b = 0 then return (T_tP, I_tP)
  else
    I <-$ I
    return (T_tP, I)

allow-corr_P  <=> max(t_A, t_B) <= t* - 2
finished_P    <=> t_P >= t* + Delta_CKA

CKA is (t, Delta, epsilon)-secure if for all t-attackers A,
  Adv_CKA_ror,Delta(A) <= epsilon
```

Lean side, exact declarations:

```
def CKA.Figure3.figure3GuessExp
    [SampleableType SharedKey] [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState]
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
    [SampleableType SharedKey] [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState]
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (tStar delta : ℕ)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState) : ℝ :=
  (figure3GuessExp cka tStar delta adversary).boolBiasAdvantage

def CKA.Figure3.Figure3CKASecurePaper
    [SampleableType SharedKey] [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState]
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (delta : ℕ) (ε : ℝ) : Prop :=
  ∀ (tStar : ℕ)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState),
    figure3GuessAdvantage cka tStar delta adversary ≤ ε
```

The paper's challenge oracle also has a direct executable counterpart. The
paper branch on the hidden bit becomes the `challengeIsRandom` branch inside
the oracle implementation:

Paper side, normalized challenge branch:

```
chall-P
  t_P++
  req t_P = t*
  (gamma', T_tP, I_tP) <-$ CKA-S(gamma)
  if b = 0 then return (T_tP, I_tP)
  else
    I <-$ I
    return (T_tP, I)
```

Lean side, exact branch from `ckaGameQueryImpl`:

```
| .challenge p => do
    let st ← get
    if st.gameEnded then pure none
    else match st.phase with
    | .awaitingSend p' =>
      if p = p' ∧ st.epochOf p + 1 = st.tStar ∧ !st.challengeUsed then do
        let coins ← liftM ($ᵗ SendCoins : ProbComp SendCoins)
        match st.stateOf p with
        | .inl ss => do
          let (rs', msg, realOutput) := cka.sendDet ss coins
          let output ← if st.challengeIsRandom
            then liftM ($ᵗ Output : ProbComp Output)
            else pure realOutput
          let st' := (st.setStateOf p (.inr rs')).incEpoch p
          set { st' with
            phase := .awaitingReceive p.other,
            pendingMsg := some msg,
            challengeUsed := true }
          pure (some (msg, output))
        | .inr _ => pure none
      else pure none
    | _ => pure none
```

The auxiliary predicates still matter, but they should be read in the right
order:

- `CKA.CKASecure` is the single-epoch warmup predicate;
- `CKA.CKASecureDelta` is the restricted multi-epoch auxiliary predicate;
- `CKA.Figure3.Figure3CKASecure` is the helper two-game version of the real
  Figure 3 surface.
:::

:::theorem "theorem3_map" (lean := "CKA.ddh_implies_cka_security_single_epoch, CKA.ddh_implies_figure3_cka_security") (parent := "correspondence_core") (tags := "theorem3, correspondence") (effort := "medium") (priority := "high")
The paper's Theorem 3 appears in two useful Lean forms: the single-epoch
epsilon wrapper `ddh_implies_cka_security_single_epoch` and the paper-facing
Figure 3 theorem `ddh_implies_figure3_cka_security`. The second is the one that
matches the statement readers should compare directly against the paper.

Paper side, normalized:

```
Assume G is (t, epsilon)-DDH-secure.
Then the DDH-based CKA scheme is (t, Delta, epsilon)-secure with Delta = 1.
```

Lean side, exact theorem:

```
theorem CKA.ddh_implies_figure3_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    Figure3.Figure3CKASecurePaper (ddhCKAWithCoins (F := F) g) 1 ε
```

The Lean theorem is more explicit about the structure that the paper leaves
implicit:

- the cyclic-group assumption becomes `hg : Function.Bijective (fun a => a • g)`;
- the CKA instance is the concrete declaration `ddhCKAWithCoins (F := F) g`;
- the paper's Definition 13 target is the proposition
  `Figure3.Figure3CKASecurePaper ... 1 ε`;
- the proof packages the pointwise reduction
  `figure3GuessAdvantage_le_ddhAdvantage`.
:::

One final translation point deserves emphasis. The paper writes the group as a
cyclic group generated by `g`. In the Lean development this is expressed by the
hypothesis `Function.Bijective (fun a => a • g)`. That hypothesis is what lets
the random DDH branch, which samples a scalar and then maps it through `a • g`,
match the CKA random branch, which samples uniformly from the group directly.

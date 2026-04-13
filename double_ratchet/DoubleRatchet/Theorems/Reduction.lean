/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Figure3Game
import DoubleRatchet.Constructions.DDHCKA
import VCVio.OracleComp.SimSemantics.PreservesInv
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# DDH → CKA Reduction (Theorem 3, Core)

The core of the Theorem 3 proof from Alwen-Coretti-Dodis (2020), p.22.
Implements the DDH adversary that simulates the Figure 3 CKA game
with DDH values embedded at the challenge window.

## Reduction strategy

The DDH adversary receives `(g, a•g, b•g, c•g)` from the DDH challenger
and simulates the Figure 3 game for an adaptive CKA adversary:

- **Epoch `t*-1`**: embed `a•g` as the CKA message
- **Epoch `t*`** (challenge): embed `b•g` as message, `c•g` as output key
- **Epoch `t*+1`**: sample fresh `x'`, use `x'•g` / `x'•(b•g)`
- **All other epochs**: simulate honestly (reduction knows all scalars)

If `c = a*b` (real DDH), `c•g` is the genuine CKA key.
If `c` is random, the key is random — matching the CKA random game.

## Symbolic state

The reduction tracks party states symbolically via `RedPub` / `RedRecv`,
recording whether the reduction knows the underlying scalar. This avoids
storing dummy values for unknown DDH exponents and makes the security
argument transparent.

## Unreachable branches

When corruption is requested for a party holding a symbolic unknown
(`aSec` / `bSec`), `stateToConc` returns `none`. The Figure 3 guards
(`allow-corr` and `finished_P`) ensure this never occurs during the DDH
window. This is formalized separately via `QueryImpl.PreservesInv`.
-/

set_option autoImplicit false

open OracleComp DiffieHellman OracleComp.ProgramLogic.Relational

namespace CKA

namespace Reduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

open Figure3

/-! ## Symbolic state types -/

/-- Symbolic sender state for the reduction. Tracks what the reduction
knows about a party's public key (the peer's DH share).

- `known x`: public key is `x • g`, scalar `x` known to reduction
- `aPub`: public key is `a • g` (DDH challenge), scalar `a` unknown
- `bPub`: public key is `b • g` (DDH challenge), scalar `b` unknown -/
inductive RedPub (F : Type) where
  | known : F → RedPub F
  | aPub
  | bPub
  deriving Inhabited

/-- Symbolic receiver state for the reduction. Tracks what the reduction
knows about a party's secret scalar.

- `known x`: secret is `x : F`, known to reduction
- `aSec`: secret is `a` (DDH exponent), unknown to reduction
- `bSec`: secret is `b` (DDH exponent), unknown to reduction -/
inductive RedRecv (F : Type) where
  | known : F → RedRecv F
  | aSec
  | bSec
  deriving Inhabited

/-! ## Interpretation functions -/

/-- Interpret a symbolic public value as an actual group element using the
DDH challenge values `(g, aG, bG)`. -/
def pubVal (g aG bG : G) : RedPub F → G
  | .known x => x • g
  | .aPub => aG
  | .bPub => bG

/-- Convert a symbolic party state to a concrete `G ⊕ F` value. Returns `none`
for symbolic unknowns (`aSec`, `bSec`) — these branches are unreachable
under the Figure 3 corruption guards. -/
def stateToConc (g aG bG : G) : RedPub F ⊕ RedRecv F → Option (G ⊕ F)
  | .inl (.known x) => some (.inl (x • g))
  | .inl .aPub => some (.inl aG)
  | .inl .bPub => some (.inl bG)
  | .inr (.known x) => some (.inr x)
  | .inr .aSec => none
  | .inr .bSec => none

/-! ## Ghost interpretation (proof-only) -/

section GhostInterp

variable {F : Type} [Field F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-- Ghost interpretation of a symbolic public value using the sampled DDH
exponents `a` and `b`. Unlike `pubVal` (which uses the DDH challenge group
elements `aG, bG`), this function uses the actual scalars — it is total and
used only in proofs, not in the executable reduction. -/
def redPubToConc (g : G) (a b : F) : RedPub F → G
  | .known x => x • g
  | .aPub => a • g
  | .bPub => b • g

/-- Ghost interpretation of a symbolic receiver secret using the sampled DDH
exponents. Total — used in proofs only. -/
def redRecvToConc (a b : F) : RedRecv F → F
  | .known x => x
  | .aSec => a
  | .bSec => b

/-- Ghost interpretation of a full symbolic party state as a concrete
`SenderState ⊕ ReceiverState` value. For DDH-CKA this is `G ⊕ F`. -/
def ghostInterpPartyState (g : G) (a b : F) : RedPub F ⊕ RedRecv F → G ⊕ F
  | .inl pub => .inl (redPubToConc g a b pub)
  | .inr recv => .inr (redRecvToConc a b recv)

/-- `pubVal g (a•g) (b•g) = redPubToConc g a b`: the execution-time
interpretation agrees with the ghost interpretation when the DDH challenge
values are the actual DDH group elements. -/
theorem redPubToConc_eq_pubVal (g : G) (a b : F) (pub : RedPub F) :
    redPubToConc g a b pub = pubVal g (a • g) (b • g) pub := by
  cases pub <;> rfl

end GhostInterp

/-! ## Reduction state -/

/-- Challenger state for the DDH → CKA reduction. Mirrors `Figure3.CKAGameState`
but stores symbolic states (`RedPub ⊕ RedRecv`) instead of concrete `G ⊕ F`.

No `challengeIsRandom` field — the DDH challenger controls real vs random
via the `c` value in the DDH triple. -/
structure RedState (F : Type) where
  /-- Symbolic state of party A. -/
  stateA : RedPub F ⊕ RedRecv F
  /-- Symbolic state of party B. -/
  stateB : RedPub F ⊕ RedRecv F
  /-- Epoch counter for party A. -/
  epochA : ℕ
  /-- Epoch counter for party B. -/
  epochB : ℕ
  /-- Challenge epoch `t*`. -/
  tStar : ℕ
  /-- Healing parameter `Δ`. -/
  delta : ℕ
  /-- Current phase of the ping-pong protocol. -/
  phase : GamePhase
  /-- Pending message from the last send (symbolic tag). -/
  pendingMsg : Option (RedPub F)
  /-- Whether the challenge oracle has been used. -/
  challengeUsed : Bool
  /-- Party A's state was revealed post-challenge. -/
  corruptedPostChalA : Bool
  /-- Party B's state was revealed post-challenge. -/
  corruptedPostChalB : Bool

instance : Inhabited (RedState F) where
  default := {
    stateA := .inl default
    stateB := .inr default
    epochA := 0
    epochB := 0
    tStar := 0
    delta := 0
    phase := .awaitingSend .A
    pendingMsg := none
    challengeUsed := false
    corruptedPostChalA := false
    corruptedPostChalB := false
  }

/-! ## State accessors -/

section StateAccess

variable {F : Type}

def RedState.redStateOf (st : RedState F) (p : Party) :
    RedPub F ⊕ RedRecv F :=
  match p with
  | .A => st.stateA
  | .B => st.stateB

def RedState.setRedStateOf (st : RedState F) (p : Party)
    (s : RedPub F ⊕ RedRecv F) : RedState F :=
  match p with
  | .A => { st with stateA := s }
  | .B => { st with stateB := s }

def RedState.redEpochOf (st : RedState F) (p : Party) : ℕ :=
  match p with
  | .A => st.epochA
  | .B => st.epochB

def RedState.incRedEpoch (st : RedState F) (p : Party) : RedState F :=
  match p with
  | .A => { st with epochA := st.epochA + 1 }
  | .B => { st with epochB := st.epochB + 1 }

end StateAccess

/-! ## Shared Figure 3 guard semantics -/

section Guards

variable {F : Type}

/-- Forget the DDH-specific interpretation and reuse the Figure 3 control-state
semantics on symbolic states directly. The `challengeIsRandom` field does not
affect the guard predicates and is fixed to `false`. -/
def RedState.toFigure3State (st : RedState F) :
    Figure3.CKAGameState (RedPub F) (RedRecv F) (RedPub F) :=
  { stateA := st.stateA
    stateB := st.stateB
    epochA := st.epochA
    epochB := st.epochB
    tStar := st.tStar
    delta := st.delta
    challengeIsRandom := false
    phase := st.phase
    pendingMsg := st.pendingMsg
    challengeUsed := st.challengeUsed
    corruptedPostChalA := st.corruptedPostChalA
    corruptedPostChalB := st.corruptedPostChalB }

@[simp] theorem RedState.toFigure3State_incRedEpoch (st : RedState F) (p : Party) :
    (st.incRedEpoch p).toFigure3State = (st.toFigure3State).incEpoch p := by
  cases p <;> rfl

/-- End-of-game: challenge used and both parties corrupted post-challenge. -/
def RedState.gameEnded (st : RedState F) : Bool :=
  st.toFigure3State.gameEnded

/-- Shared `allow-corr` predicate imported from the Figure 3 game. -/
def RedState.allowCorr (st : RedState F) : Prop :=
  Figure3.allowCorrFig3 st.toFigure3State

/-- Shared `finished_P` predicate imported from the Figure 3 game. -/
def RedState.finishedParty (st : RedState F) (p : Party) : Prop :=
  Figure3.finishedParty st.toFigure3State p

/-- Shared corruption-permission predicate imported from the Figure 3 game. -/
def RedState.corruptionPermitted (st : RedState F) (p : Party) : Prop :=
  Figure3.corruptionPermittedFig3 st.toFigure3State p

/-- Shared post-increment corruption check imported from the Figure 3 game. -/
def RedState.allowCorrPostIncrement (st : RedState F) (p : Party) : Prop :=
  Figure3.allowCorrPostIncrement st.toFigure3State p

instance (st : RedState F) : Decidable st.allowCorr :=
  by
    unfold RedState.allowCorr
    exact inferInstanceAs (Decidable (Figure3.allowCorrFig3 _))

instance (st : RedState F) (p : Party) : Decidable (st.finishedParty p) := by
  unfold RedState.finishedParty
  exact inferInstanceAs (Decidable (Figure3.finishedParty _ p))

instance (st : RedState F) (p : Party) : Decidable (st.corruptionPermitted p) :=
  by
    unfold RedState.corruptionPermitted
    exact inferInstanceAs (Decidable (Figure3.corruptionPermittedFig3 _ p))

instance (st : RedState F) (p : Party) :
    Decidable (st.allowCorrPostIncrement p) := by
  unfold RedState.allowCorrPostIncrement
  exact inferInstanceAs (Decidable (Figure3.allowCorrPostIncrement _ p))

/-- Mark that party `p` was corrupted post-challenge. -/
def RedState.setCorruptedPostChal (st : RedState F) (p : Party) : RedState F :=
  match p with
  | .A => { st with corruptedPostChalA := true }
  | .B => { st with corruptedPostChalB := true }

@[simp] theorem RedState.toFigure3State_setCorruptedPostChal
    (st : RedState F) (p : Party) :
    (st.setCorruptedPostChal p).toFigure3State =
      (st.toFigure3State).setCorruptedPostChal p := by
  cases p <;> rfl

end Guards

/-! ## Initial state -/

/-- Initial reduction state from shared key `k` and challenge epoch `tStar`.
Party A starts as sender with `known k` (public key `k•g`),
party B starts as receiver with `known k` (secret scalar `k`).
Healing parameter is fixed to `Δ = 1`. -/
def initRedState (k : F) (tStar : ℕ) : RedState F :=
  { stateA := .inl (.known k)
    stateB := .inr (.known k)
    epochA := 0
    epochB := 0
    tStar := tStar
    delta := 1
    phase := .awaitingSend .A
    pendingMsg := none
    challengeUsed := false
    corruptedPostChalA := false
    corruptedPostChalB := false }

/-- Initial reduction state for `tStar = 1`, where the pre-challenge epoch
`t*-1 = 0` is the initialization (paper p.22). The DDH challenge value `aG`
is embedded directly into the initial configuration:
- Party A starts as sender with `.aPub` (public key `aG`, scalar `a` unknown)
- Party B starts as receiver with `.aSec` (secret `a`, unknown)

No shared key `k` is sampled — the DDH challenger provides the initial state.
The `allow-corr` condition at `tStar = 1` requires epoch ≤ -1, which is
structurally impossible, so the adversary can never corrupt the initial state. -/
def initRedStateEmbedInit : RedState F :=
  { stateA := .inl .aPub
    stateB := .inr .aSec
    epochA := 0
    epochB := 0
    tStar := 1
    delta := 1
    phase := .awaitingSend .A
    pendingMsg := none
    challengeUsed := false
    corruptedPostChalA := false
    corruptedPostChalB := false }

/-! ## Oracle implementation -/

section OracleImpl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

/-- Handle a reduction send: given symbolic sender state, DDH values, and coins,
compute the message and output key. Returns `none` if party not in sender state.

At the pre-challenge epoch (`redEpochOf p + 2 = tStar`), embeds `aG` instead
of using the supplied coins. At all other epochs, uses coins directly.

The epoch `t*+1` send (with `.bPub` sender state) is handled by the normal
path: `pubVal g aG bG .bPub = bG`, so `coins • bG` is correct. -/
private def redHandleSend (g aG bG : G) (p : Party) (coins : F) :
    StateT (RedState F) ProbComp (Option (G × G)) := do
  let st ← get
  match st.redStateOf p with
  | .inl pub =>
    if st.redEpochOf p + 2 = st.tStar then
      -- Pre-challenge epoch t*-1: embed aG
      match pub with
      | .known xPrev =>
        let output := xPrev • aG
        let st' := (st.setRedStateOf p (.inr .aSec)).incRedEpoch p
        set { st' with
          phase := .awaitingReceive p.other,
          pendingMsg := some .aPub }
        pure (some (aG, output))
      | _ => pure none  -- unreachable at t*-1
    else do
      -- Normal send: use coins
      let output := coins • pubVal g aG bG pub
      let st' := (st.setRedStateOf p (.inr (.known coins))).incRedEpoch p
      set { st' with
        phase := .awaitingReceive p.other,
        pendingMsg := some (.known coins) }
      pure (some (coins • g, output))
  | .inr _ => pure none

/-- Reduction oracle implementation. Simulates the Figure 3 CKA game for
an adaptive adversary, embedding DDH challenge values at the challenge window.

The guard logic is shared via `RedState.toFigure3State`; only the symbolic
state transitions and DDH-specific output computations are reduction-specific. -/
def redQueryImpl (g aG bG cG : G) :
    QueryImpl (ckaOracleSpec F G G G F)
      (StateT (RedState F) ProbComp)

  | .sendHonest p => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingSend p' =>
        if p = p' then do
          let coins ← liftM ($ᵗ F : ProbComp F)
          redHandleSend g aG bG p coins
        else pure none
      | _ => pure none

  | .sendBadRand p r => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingSend p' =>
        if p = p' ∧ decide (st.allowCorrPostIncrement p) then
          redHandleSend g aG bG p r
        else pure none
      | _ => pure none

  | .receive p => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingReceive p' =>
        if p = p' then
          match st.pendingMsg, st.redStateOf p with
          | some msg, .inr _ => do
            let st' := (st.setRedStateOf p (.inl msg)).incRedEpoch p
            set ({ st' with
              phase := .awaitingSend p,
              pendingMsg := none } : RedState F)
            pure (some ())
          | _, _ => pure none
        else pure none
      | _ => pure none

  | .challenge p => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingSend p' =>
        if p = p' ∧ st.redEpochOf p + 1 = st.tStar ∧ !st.challengeUsed then
          match st.redStateOf p with
          | .inl .aPub =>
            -- DDH embedding: message = bG, output = cG
            let st' := (st.setRedStateOf p (.inr .bSec)).incRedEpoch p
            set { st' with
              phase := .awaitingReceive p.other,
              pendingMsg := some .bPub,
              challengeUsed := true }
            pure (some (bG, cG))
          | .inl (.known x) => do
            -- Normal challenge (tStar too small for DDH embedding)
            let coins ← liftM ($ᵗ F : ProbComp F)
            let output := coins • (x • g)
            let st' := (st.setRedStateOf p (.inr (.known coins))).incRedEpoch p
            set { st' with
              phase := .awaitingReceive p.other,
              pendingMsg := some (.known coins),
              challengeUsed := true }
            pure (some (coins • g, output))
          | _ => pure none
        else pure none
      | _ => pure none

  | .corrupt p => do
      let st ← get
      if st.gameEnded then pure none
      else if decide (st.corruptionPermitted p) then do
        if st.challengeUsed && decide (st.finishedParty p) then
          modify fun s => s.setCorruptedPostChal p
        pure (stateToConc g aG bG (st.redStateOf p))
      else
        pure none

end OracleImpl

/-! ## Combined oracle implementations -/

/-- Full oracle implementation seen by the DDH reduction: private randomness
from `unifSpec` plus the symbolic Figure 3 game oracles. -/
def reductionFigure3Impl
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [Inhabited F]
    {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [Inhabited G]
    (g aG bG cG : G) :
    QueryImpl (Figure3.Figure3OracleSpec F G G G F)
      (StateT (RedState F) ProbComp) :=
  let unifImpl :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (RedState F) ProbComp)
  unifImpl + redQueryImpl (F := F) g aG bG cG

/-- Full concrete oracle implementation used by the adaptive Figure 3
adversary. The real or random branch is selected by the
`challengeIsRandom` flag stored in the concrete game state. -/
def concreteFigure3Impl
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [Inhabited F]
    {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [Inhabited G]
    (g : G) :
    QueryImpl (Figure3.Figure3OracleSpec F G G G F)
      (StateT (Figure3.CKAGameState G F G) ProbComp) :=
  let unifImpl :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Figure3.CKAGameState G F G) ProbComp)
  unifImpl + Figure3.ckaGameQueryImpl
    (SharedKey := F) (SenderState := G) (ReceiverState := F)
    (Msg := G) (Output := G) (SendCoins := F)
    (ddhCKAWithCoins (F := F) g)

/-! ## Simulation relation -/

/-- The symbolic reduction state matches a concrete `CKAGameState` under
the ghost interpretation with DDH exponents `a` and `b`. This is the
simulation relation for the distribution equivalence proof.

All control fields must match exactly. Party states and pending messages
are related via the ghost interpretation. The `challengeIsRandom` field
of the concrete state is unconstrained — the DDH challenger controls
real vs random via the `c` value. -/
def redStateMatches (g : G) (a b : F) (rst : RedState F)
    (cst : Figure3.CKAGameState G F G) : Prop :=
  ghostInterpPartyState g a b rst.stateA = cst.stateA ∧
  ghostInterpPartyState g a b rst.stateB = cst.stateB ∧
  rst.epochA = cst.epochA ∧
  rst.epochB = cst.epochB ∧
  rst.tStar = cst.tStar ∧
  rst.delta = cst.delta ∧
  rst.phase = cst.phase ∧
  rst.pendingMsg.map (redPubToConc g a b) = cst.pendingMsg ∧
  rst.challengeUsed = cst.challengeUsed ∧
  rst.corruptedPostChalA = cst.corruptedPostChalA ∧
  rst.corruptedPostChalB = cst.corruptedPostChalB

/-! ## Phase 1 bridge lemmas -/

section Scaffold

variable {F : Type} [Field F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-- The generic reduction initial state matches the canonical Figure 3 initial
state for DDH-CKA. The hidden-bit branch may be either value because
`redStateMatches` intentionally abstracts over `challengeIsRandom`. -/
theorem initRedState_matches_initialState
    (g : G) (k : F) (tStar : ℕ) (challengeIsRandom : Bool) :
    redStateMatches g k k (initRedState k tStar)
      (Figure3.initialState (SenderState := G) (ReceiverState := F) (Msg := G)
        (k • g) k tStar 1 challengeIsRandom) := by
  simp [redStateMatches, initRedState, Figure3.initialState, ghostInterpPartyState,
    redPubToConc, redRecvToConc]

/-- The special `t* = 1` reduction initial state matches the canonical
Figure 3 initial state obtained by embedding the DDH value `a • g` directly
into the starting configuration. -/
theorem initRedStateEmbedInit_matches_initialState
    (g : G) (a b : F) (challengeIsRandom : Bool) :
    redStateMatches g a b initRedStateEmbedInit
      (Figure3.initialState (SenderState := G) (ReceiverState := F) (Msg := G)
        (a • g) a 1 1 challengeIsRandom) := by
  simp [redStateMatches, initRedStateEmbedInit, Figure3.initialState, ghostInterpPartyState,
    redPubToConc, redRecvToConc]

/-- `redStateMatches` transports `allow-corr` between the symbolic reduction
state and the concrete Figure 3 state. -/
lemma redStateMatches_allowCorr_iff
    (g : G) (a b : F) (rst : RedState F) (cst : Figure3.CKAGameState G F G)
    (hMatch : redStateMatches g a b rst cst) :
    rst.allowCorr ↔ Figure3.allowCorrFig3 cst := by
  rcases hMatch with ⟨_, _, hA, hB, ht, _, _, _, _, _, _⟩
  simp [RedState.allowCorr, Figure3.allowCorrFig3, RedState.toFigure3State, hA, hB, ht]

/-- `redStateMatches` transports `finished_P` between the symbolic reduction
state and the concrete Figure 3 state. -/
lemma redStateMatches_finishedParty_iff
    (g : G) (a b : F) (rst : RedState F) (cst : Figure3.CKAGameState G F G)
    (p : Party) (hMatch : redStateMatches g a b rst cst) :
    rst.finishedParty p ↔ Figure3.finishedParty cst p := by
  rcases hMatch with ⟨_, _, hA, hB, ht, hd, _, _, _, _, _⟩
  cases p <;>
    simp [RedState.finishedParty, Figure3.finishedParty, RedState.toFigure3State, hA, hB, ht, hd]

/-- `redStateMatches` transports corruption permission between the symbolic
reduction state and the concrete Figure 3 state. -/
lemma redStateMatches_corruptionPermitted_iff
    (g : G) (a b : F) (rst : RedState F) (cst : Figure3.CKAGameState G F G)
    (p : Party) (hMatch : redStateMatches g a b rst cst) :
    rst.corruptionPermitted p ↔ Figure3.corruptionPermittedFig3 cst p := by
  constructor
  · intro h
    cases h with
    | inl hAllow =>
        exact Or.inl ((redStateMatches_allowCorr_iff g a b rst cst hMatch).mp hAllow)
    | inr hFinished =>
        exact Or.inr ((redStateMatches_finishedParty_iff g a b rst cst p hMatch).mp hFinished)
  · intro h
    cases h with
    | inl hAllow =>
        exact Or.inl ((redStateMatches_allowCorr_iff g a b rst cst hMatch).mpr hAllow)
    | inr hFinished =>
        exact Or.inr ((redStateMatches_finishedParty_iff g a b rst cst p hMatch).mpr hFinished)

/-- `redStateMatches` also transports the end-of-game flag. -/
lemma redStateMatches_gameEnded_eq
    (g : G) (a b : F) (rst : RedState F) (cst : Figure3.CKAGameState G F G)
    (hMatch : redStateMatches g a b rst cst) :
    rst.gameEnded = cst.gameEnded := by
  rcases hMatch with ⟨_, _, _, _, _, _, _, _, hChallenge, hCorrA, hCorrB⟩
  simp [RedState.gameEnded, Figure3.CKAGameState.gameEnded, RedState.toFigure3State,
    hChallenge, hCorrA, hCorrB]

end Scaffold

/-! ## Reduction invariant -/

/-- Reduction invariant: if corruption is permitted for party `p`, then
the party's symbolic state is representable as concrete (`stateToConc`
returns `some`). This guarantees the `none` branches in `stateToConc`
are never reached during valid game execution.

Proved separately via `QueryImpl.PreservesInv`. -/
def RedInv (g aG bG : G) (st : RedState F) : Prop :=
  ∀ p, st.corruptionPermitted p →
    (stateToConc (F := F) g aG bG (st.redStateOf p)).isSome

/-- The reduction oracle preserves the no-illegal-corruption invariant:
every oracle handler starting from a state satisfying `RedInv` produces a
post-state satisfying `RedInv`. This guarantees the `none` branches in
`stateToConc` are never reached during valid game execution.

The proof follows from the paper's healing argument (p.20-22):
- `allow-corr` blocks corruption in the challenge window
- Unknown exponents `.aSec`/`.bSec` exist only at epochs `[t*-1, t*]`
- `finished_P` allows corruption only after epoch `t* + Δ`, by which time
  the unknown exponents have been overwritten with known values -/
theorem redQueryImpl_preservesRedInv
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [Inhabited F]
    {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [Inhabited G]
    (g aG bG cG : G) :
    QueryImpl.PreservesInv (redQueryImpl (F := F) g aG bG cG)
      (RedInv (F := F) g aG bG) := by
  sorry

end Reduction

/-! ## DDH → CKA reduction adversary -/

/-- Reduction from Figure 3 adversary to DDH adversary (Theorem 3, p.22).

The DDH adversary receives `(g, a•g, b•g, c•g)` from the DDH challenger and
simulates the Figure 3 game with DDH values embedded at the challenge window:

- Epoch `t*-1`: embed `a•g` into party B's CKA message `T_{t*-1}`
- Epoch `t*` (challenge): embed `b•g` as message `T_{t*}`, `c•g` as output key `I_{t*}`
- Epoch `t*+1`: sample fresh `x' ← F`, set `T_{t*+1} = x'•g`, `I_{t*+1} = x'•(b•g)`
- Other epochs: simulate honestly (reduction knows the init key)

When `tStar = 1`, the pre-challenge epoch `t*-1 = 0` is the initialization:
the DDH value `aG` is embedded directly into the initial configuration via
`initRedStateEmbedInit` (no shared key `k` is sampled).

If `c = a*b` (real DDH), `c•g` is the genuine CKA key. If `c` is random, so is
the key. The adversary's Figure 3 advantage equals the DDH advantage. -/
def figure3AdvToDDHAdv
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [Inhabited F]
    {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    [Inhabited G]
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

/-! ## Distribution equality lemmas (Theorem 3 proof chain)

The core of Theorem 3: the DDH reduction correctly simulates the Figure 3
CKA game. Proved via `relTriple_simulateQ_run` with `R_state := redStateMatches`
and per-query `RelTriple` correspondence for each oracle handler.

The proof chain is:
1. `reductionFigure3Impl_real_relTriple` handles the real-branch per-query
   correspondence.
2. `reductionFigure3Sim_real_run'_relTriple` lifts that correspondence through
   `simulateQ`.
3. `figure3Exp_real_eq_ddhExpReal` and `figure3Exp_rand_eq_ddhExpRand` package
   the real and random branches as distribution equalities.
4. `figure3Advantage_le_ddhAdvantage` follows from those equalities.
-/

section DistributionEquality

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

/-- Phase-1 scaffold theorem: real-branch query-by-query correspondence between
the full reduction oracle implementation and the concrete Figure 3 oracle
implementation. This is the main local theorem later consumed by
`relTriple_simulateQ_run'`. -/
theorem reductionFigure3Impl_real_relTriple
    (g : G) (a b : F)
    (t : (Figure3.Figure3OracleSpec F G G G F).Domain)
    (rst : Reduction.RedState F)
    (cst : Figure3.CKAGameState G F G)
    (hMatch : Reduction.redStateMatches g a b rst cst)
    (hInv : Reduction.RedInv g (a • g) (b • g) rst)
    (hReal : cst.challengeIsRandom = false) :
    RelTriple
      (((Reduction.reductionFigure3Impl (F := F) g (a • g) (b • g) ((a * b) • g)) t).run rst)
      (((Reduction.concreteFigure3Impl (F := F) g) t).run cst)
      (fun p₁ p₂ =>
        p₁.1 = p₂.1 ∧
        Reduction.redStateMatches g a b p₁.2 p₂.2 ∧
        Reduction.RedInv g (a • g) (b • g) p₁.2) := by
  sorry

/-- Phase-1 scaffold theorem: lifting the real-branch per-query correspondence
through `simulateQ` yields equality of the adversary output bit. The final
distribution-equality theorem `figure3Exp_real_eq_ddhExpReal` will later be
obtained by combining this theorem with the initial-state bridge lemmas and
the DDH sampling wrapper. -/
theorem reductionFigure3Sim_real_run'_relTriple
    (g : G) (a b : F)
    (A : Figure3.Figure3Adversary F G G G F)
    (rst : Reduction.RedState F)
    (cst : Figure3.CKAGameState G F G)
    (hMatch : Reduction.redStateMatches g a b rst cst)
    (hInv : Reduction.RedInv g (a • g) (b • g) rst)
    (hReal : cst.challengeIsRandom = false) :
    RelTriple
      ((simulateQ (Reduction.reductionFigure3Impl (F := F) g (a • g) (b • g) ((a * b) • g))
        A).run' rst)
      ((simulateQ (Reduction.concreteFigure3Impl (F := F) g) A).run' cst)
      (EqRel Bool) := by
  sorry

/-- Real DDH experiment with the reduction equals the real Figure 3 game.

When `c = a*b` (real DDH), the reduction's oracle simulation produces the
same output distribution as the concrete CKA game with `challengeIsRandom = false`:
- At the pre-challenge epoch, the reduction uses `a` as coins (uniform, same distribution)
- At the challenge epoch, `cG = (ab)•g = b • (a•g)` equals the real CKA output
- All other epochs are simulated honestly with sampled coins

The proof uses `relTriple_simulateQ_run` with `R_state := redStateMatches g a b`
to lift per-query correspondence to full simulation equivalence. -/
theorem figure3Exp_real_eq_ddhExpReal
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ) (A : Figure3.Figure3Adversary F G G G F) :
    evalDist (Figure3.figure3Exp (ddhCKAWithCoins (F := F) g) tStar 1 false A) =
      evalDist (ddhExpReal (F := F) g (figure3AdvToDDHAdv (tStar, A))) := by
  sorry

/-- Random DDH experiment with the reduction equals the random Figure 3 game.

When `c` is random (random DDH), the reduction outputs `cG = c•g` at the
challenge epoch. Since `· • g` is bijective, `c•g` with `c ← F` is uniformly
distributed over `G`, matching the concrete game's `$ᵗ G` random replacement.

This is the only lemma in the chain that requires bijectivity `hg`. -/
theorem figure3Exp_rand_eq_ddhExpRand
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ) (A : Figure3.Figure3Adversary F G G G F) :
    evalDist (Figure3.figure3Exp (ddhCKAWithCoins (F := F) g) tStar 1 true A) =
      evalDist (ddhExpRand (F := F) g (figure3AdvToDDHAdv (tStar, A))) := by
  sorry

end DistributionEquality

end CKA

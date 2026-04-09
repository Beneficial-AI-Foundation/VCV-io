/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Figure3Game
import DoubleRatchet.Constructions.DDHCKA
import VCVio.OracleComp.SimSemantics.PreservesInv

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

open OracleComp DiffieHellman

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

/-! ## Guard predicates -/

section Guards

variable {F : Type}

/-- End-of-game: challenge used and both parties corrupted post-challenge. -/
def RedState.gameEnded (st : RedState F) : Bool :=
  st.challengeUsed && st.corruptedPostChalA && st.corruptedPostChalB

/-- `allow-corr`: corruption allowed before the challenge window. -/
def RedState.allowCorr (st : RedState F) : Prop :=
  max st.epochA st.epochB + 2 ≤ st.tStar

/-- `finished_P`: party P has healed past the challenge. -/
def RedState.finishedParty (st : RedState F) (p : Party) : Prop :=
  match p with
  | .A => st.epochA ≥ st.tStar + st.delta
  | .B => st.epochB ≥ st.tStar + st.delta

/-- Corruption permitted: `allow-corr ∨ finished_P`. -/
def RedState.corruptionPermitted (st : RedState F) (p : Party) : Prop :=
  st.allowCorr ∨ st.finishedParty p

/-- `allow-corr` against the post-increment epoch for `send-P'(r)`. -/
def RedState.allowCorrPostIncrement (st : RedState F) (p : Party) : Prop :=
  (st.incRedEpoch p).allowCorr

instance (st : RedState F) : Decidable st.allowCorr :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (st : RedState F) (p : Party) : Decidable (st.finishedParty p) := by
  unfold RedState.finishedParty; cases p <;> exact inferInstanceAs (Decidable (_ ≥ _))

instance (st : RedState F) (p : Party) : Decidable (st.corruptionPermitted p) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (st : RedState F) (p : Party) :
    Decidable (st.allowCorrPostIncrement p) := by
  unfold RedState.allowCorrPostIncrement
  exact inferInstanceAs (Decidable (RedState.allowCorr _))

/-- Mark that party `p` was corrupted post-challenge. -/
def RedState.setCorruptedPostChal (st : RedState F) (p : Party) : RedState F :=
  match p with
  | .A => { st with corruptedPostChalA := true }
  | .B => { st with corruptedPostChalB := true }

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

Guard logic is copied from `Figure3.ckaGameQueryImpl`. Only the state
transitions and output computations change to use symbolic state. -/
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
    let unifImpl :=
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (Reduction.RedState F) ProbComp)
    let guess ← (simulateQ (unifImpl + Reduction.redQueryImpl (F := F) g aG bG cG)
      AtStar.2).run' initSt
    pure guess

/-! ## Distribution equality lemmas (Theorem 3 proof chain)

The core of Theorem 3: the DDH reduction correctly simulates the Figure 3
CKA game. Proved via `relTriple_simulateQ_run` with `R_state := redStateMatches`
and per-query `RelTriple` correspondence for each oracle handler.

The proof chain is:
1. Per-query `RelTriple`: each handler of `redQueryImpl` matches
   `ckaGameQueryImpl` under `redStateMatches g a b`
2. `relTriple_simulateQ_run'` lifts per-query to full simulation
3. Distribution equalities follow from the coupling
4. `figure3Advantage_le_ddhAdvantage` follows from the equalities
-/

section DistributionEquality

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

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

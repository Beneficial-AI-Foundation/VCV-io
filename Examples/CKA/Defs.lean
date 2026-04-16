import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# Continuous Key Agreement (CKA)

A CKA is a two-party stateful protocol where two parties A and B take turns exchanging
protocol messages. Every send/receive pair yields a fresh shared epoch key.

- `CKAScheme` — CKA syntax.
- `CKAScheme.correctnessExp` — correctness game.
- `CKAScheme.securityExp` — key-indistinguishability game.

## References

- [ACD19] Alwen, Coretti, Dodis.
  *The Double Ratchet: Security Notions, Proofs, and Modularization for the Signal Protocol.*
  EUROCRYPT 2019, https://eprint.iacr.org/2018/1037.pdf
- [TripleRatchet]  Dodis, Jost, Katsumata, Prest, Schmidt.
  *Triple Ratchet: A Bandwidth Efficient Hybrid-Secure Signal Protocol.*
  EUROCRYPT 2025, https://eprint.iacr.org/2025/078.pdf
- [SPQR] Auerbach, Dodis, Jost, Katsumata, Schmidt.
  *How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols:
  A Quest for A More Efficient and Secure Post-Quantum Protocol.*
  USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf
-/

open OracleSpec OracleComp ENNReal

universe u v

/-- A continuous key agreement (CKA) protocol with initial-key space `IK`,
per-party state space `St`, epoch-key space `I`, and protocol-message space `Rho`. -/
structure CKAScheme (m : Type → Type u) [Monad m] (IK St I Rho : Type) where
  initKeyGen : m IK
  initA : IK → m St
  initB : IK → m St
  sendA : St → m (Option (I × Rho × St))
  recvA : St → Rho → Option (I × St)
  sendB : St → m (Option (I × Rho × St))
  recvB : St → Rho → Option (I × St)

namespace CKAScheme

variable {m : Type → Type v} [Monad m] {IK St I Rho : Type}
  (cka : CKAScheme m IK St I Rho)

/-! ## Oracle-based games

The CKA game [ACD19, Def. 13] gives the adversary oracle access to:
- **O-Send-A / O-Send-B**
  Trigger one party to send, return `(ρ, key)`, and update the sender state.
- **O-Recv-A / O-Recv-B**
  Deliver the latest message in that direction and update the receiver state.
  *Correctness assert*: the received key must match the sender's corresponding key.
- **O-Chall-A / O-Chall-B**
  Like send, but return real key (`b = 0`) or random key (`b = 1`).
- **O-Corrupt-A / O-Corrupt-B**
  Return the current state of party A (resp. B) and record the corruption epoch.

As in [ACD19, TripleRatchet], and contrary to [SPQR], we have:
- **Alternating Communication**: the games enforce parties A and B to execute the sending and
receiving algorithms in an alternating order.

- **Fully Passive Adversary**: the adversary can neither modify nor reorder sent messages.

- **Static Challenge Epoch**: the security adversary can only challenge the key for one epoch,
which is fixed at the beginning of the security experiment.

As in [TripleRatchet, SPQR], and contrary to [ACD19], we don't consider additional oracles that
allow to corrupt the randomness of a sending party.

We define two games:
- **Correctness game**: adversary wins if receiver and sender keys don't agree.
- **Security game**: adversary wins if it can distinguish a real from a random key.
The correctness game does not use the challenge and corruption oracles.

-/

section Games

variable {IK St I Rho : Type}

/-- Trace of protocol actions observed in the CKA game. -/
inductive CKAAction where
  | sendA | recvA | sendB | recvB | challA | challB
  deriving DecidableEq, Repr

/-- The two parties in a CKA protocol. Used to parameterize the security
game by which party is challenged. -/
inductive CKAParty where
  | A | B
  deriving DecidableEq, Repr

/-- Protocol action expected next. -/
inductive CKAExpected where
  | sendA | recvB | sendB | recvA

/-- Predicate enforcincg *Alternate Communication* -/
def validStep (last : Option CKAAction) (next : CKAAction) : Bool :=
  match last, next with
  | none,         .sendA  | none,         .challA  => true
  | some .sendA,  .recvB  | some .challA, .recvB   => true
  | some .recvB,  .sendB  | some .recvB,  .challB  => true
  | some .sendB,  .recvA  | some .challB, .recvA   => true
  | some .recvA,  .sendA  | some .recvA,  .challA  => true
  | _, _ => false

/-- Game parameters fixed at the start of the security experiment. -/
structure GameParams where
  tStar : ℕ              -- epoch that adversary will challenge
  deltaCKA : ℕ           -- healing delay after state corruption
  challengedParty : CKAParty  -- which party `P ∈ {A, B}` is challenged

/-- Internal state of the CKA game.
- `stA`, `stB`: per-party protocol state.
- `lastRhoA/B`, `lastKeyA/B`: pending undelivered message and sender key.
- `b`: hidden challenge bit (security game only).
- `correct`: conjunction of all key-agreement checks so far.
- `lastAction`: enforces alternating communication.
- `tA`, `tB`: epoch counters (incremented on each send/chall/recv). -/
structure GameState (St I Rho : Type) where
  stA : St
  stB : St
  lastRhoA : Option Rho  -- latest undelivered A -> B message
  lastRhoB : Option Rho  -- latest undelivered B -> A message
  lastKeyA : Option I    -- sender key paired with `lastRhoA`
  lastKeyB : Option I    -- sender key paired with `lastRhoB`
  b : Bool
  correct : Bool
  lastAction : Option CKAAction
  tA : ℕ                 -- epoch counter for A (incremented on each send/chall/recv by A)
  tB : ℕ                 -- epoch counter for B (incremented on each send/chall/recv by B)

/-- Epoch counter for party `p`. -/
def GameState.tP (s : GameState St I Rho) : CKAParty → ℕ
  | .A => s.tA
  | .B => s.tB

/-- State of party `p`. -/
def GameState.stP (s : GameState St I Rho) : CKAParty → St
  | .A => s.stA
  | .B => s.stB

/-- Oracle spec for the CKA correctness game (send + recv only). -/
def ckaCorrectnessSpec (Rho I : Type) :=
  unifSpec                        -- Uniform randomness
  + (Unit →ₒ Option (Rho × I))   -- O-Send-A
  + (Unit →ₒ Unit)               -- O-Recv-A
  + (Unit →ₒ Option (Rho × I))   -- O-Send-B
  + (Unit →ₒ Unit)               -- O-Recv-B

/-- Oracle spec for the CKA security game (send + recv + challenge + corrupt). -/
def ckaSecuritySpec (St Rho I : Type) :=
  ckaCorrectnessSpec Rho I
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-A
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-B
  + (Unit →ₒ Option St)           -- O-Corrupt-A
  + (Unit →ₒ Option St)           -- O-Corrupt-B

/-! ### Epoch predicates -/

/-- Challenge fires when the challenged party's counter reaches `tStar`. -/
def isChallengeEpoch (gp : GameParams) (state : GameState St I Rho) : Bool :=
  state.tP gp.challengedParty == gp.tStar

/-- The other party's send just before the challenge. Due to alternating
communication with A going first:
- challenging A: B-send at `tB = tStar - 1`
- challenging B: A-send at `tA = tStar` -/
def isOtherSendBeforeChall (gp : GameParams) (state : GameState St I Rho) : Bool :=
  match gp.challengedParty with
  | .A => state.tB == gp.tStar - 1
  | .B => state.tA == gp.tStar

/-- Party `p` has healed: `tP ≥ tStar + ΔCKA`. -/
def finishedP (gp : GameParams) (party : CKAParty) (state : GameState St I Rho) : Bool :=
  gp.tStar + gp.deltaCKA ≤ state.tP party

/-- `tA ≥ t* + ΔCKA`. -/
abbrev finishedA (gp : GameParams) (state : GameState St I Rho) : Bool := finishedP gp .A state

/-- `tB ≥ t* + ΔCKA`. -/
abbrev finishedB (gp : GameParams) (state : GameState St I Rho) : Bool := finishedP gp .B state

/-- Corruption allowed before the challenge window: `max(tA, tB) + 2 ≤ tStar`. -/
def allowCorr (gp : GameParams) (state : GameState St I Rho) : Bool :=
  max state.tA state.tB + 2 ≤ gp.tStar

/-! ### Send oracles -/

/-- **O-Send-A.** `tA++; (key, ρ, stA') ← sendA(stA)`; return `(ρ, key)`. -/
def oracleSendA (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendA then
      -- tA++
      let state := { state with tA := state.tA + 1 }
      match ← liftM (cka.sendA state.stA) with
      | none => pure none
      | some (key, ρ, stA') =>
        set { state with
          stA := stA', lastRhoA := some ρ, lastKeyA := some key,
          lastAction := some .sendA }
        return some (ρ, key)
    else pure none

/-- **O-Send-B.** `tB++; (key, ρ, stB') ← sendB(stB)`; return `(ρ, key)`. -/
def oracleSendB (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .sendB then
      -- tB++
      let state := { state with tB := state.tB + 1 }
      match ← liftM (cka.sendB state.stB) with
      | none => pure none
      | some (key, ρ, stB') =>
        set { state with
          stB := stB', lastRhoB := some ρ, lastKeyB := some key,
          lastAction := some .sendB }
        return some (ρ, key)
    else pure none

/-! ### Receive oracles -/

/-- **O-Recv-A.** `tA++; (keyA, stA') ← recvA(stA, ρ)`; assert `keyA = lastKeyB`. -/
def oracleRecvA [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .recvA then
      -- tA++
      let state := { state with tA := state.tA + 1 }
      match state.lastRhoB with
      | none => pure ()
      | some ρ =>
        match cka.recvA state.stA ρ with
        | none => pure ()
        | some (keyA, stA') =>
          let ok := match state.lastKeyB with
            | some keyB => decide (some keyA = some keyB)
            | none => false
          set { state with
            stA := stA', lastRhoB := none, lastKeyB := none,
            correct := state.correct && ok, lastAction := some .recvA }
    else pure ()

/-- **O-Recv-B.** `tB++; (keyB, stB') ← recvB(stB, ρ)`; assert `keyB = lastKeyA`. -/
def oracleRecvB [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .recvB then
      -- tB++
      let state := { state with tB := state.tB + 1 }
      match state.lastRhoA with
      | none => pure ()
      | some ρ =>
        match cka.recvB state.stB ρ with
        | none => pure ()
        | some (keyB, stB') =>
          let ok := match state.lastKeyA with
            | some keyA => decide (some keyB = some keyA)
            | none => false
          set { state with
            stB := stB', lastRhoA := none, lastKeyA := none,
            correct := state.correct && ok, lastAction := some .recvB }
    else pure ()

/-! ### Challenge oracles -/

/-- **O-Chall-A.** Like `O-Send-A` but returns `b ? $ᵗ I : key` (real or
random key). Only fires when `P = A` and `tA = t*`. -/
def oracleChallA (gp : GameParams) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA then
      let state := { state with tA := state.tA + 1 }
      if gp.challengedParty == .A && isChallengeEpoch gp state then
        match ← liftM (cka.sendA state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          let outKey ← if state.b then liftM ($ᵗ I : ProbComp I) else pure key
          set { state with
            stA := stA', lastRhoA := some ρ, lastKeyA := some key,
            lastAction := some .challA }
          return some (ρ, outKey)
      else pure none
    else pure none

/-- **O-Chall-B.** Like `O-Send-B` but returns `b ? $ᵗ I : key` (real or
random key). Only fires when `P = B` and `tB = t*`. -/
def oracleChallB (gp : GameParams) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challB then
      let state := { state with tB := state.tB + 1 }
      if gp.challengedParty == .B && isChallengeEpoch gp state then
        match ← liftM (cka.sendB state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          let outKey ← if state.b then liftM ($ᵗ I : ProbComp I) else pure key
          set { state with
            stB := stB', lastRhoB := some ρ, lastKeyB := some key,
            lastAction := some .challB }
          return some (ρ, outKey)
      else pure none
    else pure none

/-! ### Corruption oracles

Following [ACD19, Def. 13, Fig. 3], corruption is allowed iff
`allowCorr ∨ finishedP` (see epoch predicates above).
-/

/-- **O-Corrupt-A.** Return `stA` if `allowCorr ∨ finishedA`. -/
def oracleCorruptA (gp : GameParams) (St I Rho : Type) :
    QueryImpl (Unit →ₒ Option St) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if allowCorr gp state || finishedA gp state then return some state.stA
    else return none

/-- **O-Corrupt-B.** `() → Option St`. Return `stB` if corruption is allowed. -/
def oracleCorruptB (gp : GameParams) (St I Rho : Type) :
    QueryImpl (Unit →ₒ Option St) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if allowCorr gp state || finishedB gp state then return some state.stB
    else return none

/-- Oracle for adversary randomness: forwards to `ProbComp`. -/
def oracleUnif (St I Rho : Type) :
    QueryImpl unifSpec (StateT (GameState St I Rho) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (GameState St I Rho) ProbComp)

/-- Oracle implementation for the correctness game. -/
def ckaCorrectnessImpl [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (ckaCorrectnessSpec Rho I) (StateT (GameState St I Rho) ProbComp) :=
  oracleUnif St I Rho
    + oracleSendA cka + oracleRecvA cka
    + oracleSendB cka + oracleRecvB cka

/-- Oracle implementation for the security game. -/
def ckaSecurityImpl (gp : GameParams) [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (ckaSecuritySpec St Rho I) (StateT (GameState St I Rho) ProbComp) :=
  ckaCorrectnessImpl cka
    + oracleChallA gp cka + oracleChallB gp cka
    + oracleCorruptA gp St I Rho + oracleCorruptB gp St I Rho

/-- Correctness adversary: send + recv oracles only. -/
abbrev CorrectnessAdversary (Rho I : Type) := OracleComp (ckaCorrectnessSpec Rho I) Bool

/-- Security adversary: send + recv + challenge + corruption oracles. -/
abbrev SecurityAdversary (St Rho I : Type) := OracleComp (ckaSecuritySpec St Rho I) Bool

/-! ### Correctness game -/

/-- Initial game state. -/
def initGameState (stA stB : St) (b : Bool) : GameState St I Rho :=
  { stA, stB, lastRhoA := none, lastRhoB := none,
    lastKeyA := none, lastKeyB := none,
    b, correct := true, lastAction := none,
    tA := 0, tB := 0 }

def correctnessExp [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CorrectnessAdversary Rho I) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let (_, state) ← (simulateQ (ckaCorrectnessImpl cka) adversary).run
    (initGameState stA stB false)
  return state.correct

/-! ### Security game -/

/-- Security game parameterized by `GameParams` [ACD19, Def. 13, Fig. 3]. -/
def securityExp [SampleableType I] [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : SecurityAdversary St Rho I)
    (gp : GameParams) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (ckaSecurityImpl gp cka) adversary).run
    (initGameState stA stB b)
  return (b == b')

/-- Security experiment with a fixed challenge bit `b` (not sampled uniformly).
Returns the adversary's raw guess `b'` (not `b == b'`). -/
def securityExpFixedBit [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : SecurityAdversary St Rho I)
    (b : Bool) (gp : GameParams) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let (b', _) ← (simulateQ (ckaSecurityImpl gp cka) adversary).run
    (initGameState stA stB b)
  return b'

/-- The single-game CKA experiment can be decomposed as a uniform-bit branch over
the two fixed-bit experiments. Proved by swapping `b ← $ᵗ Bool` past the three
initialization steps using `probEvent_bind_bind_swap` (cf. `ddhExp_probOutput_eq_branch`
for the analogous DDH result). -/
private lemma securityExp_probOutput_eq_branch [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : SecurityAdversary St Rho I) (gp : GameParams) :
    Pr[= true | securityExp cka adversary gp] =
    Pr[= true | do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let z ← if b then securityExpFixedBit cka adversary true gp
               else securityExpFixedBit cka adversary false gp
      pure (b == z)] := by
  unfold securityExp
  simp only [← probEvent_eq_eq_probOutput]
  rw [probEvent_bind_congr fun ik _ =>
    probEvent_bind_congr fun stA _ =>
    probEvent_bind_bind_swap _ _ _ _]
  rw [probEvent_bind_congr fun ik _ =>
    probEvent_bind_bind_swap _ _ _ _]
  rw [probEvent_bind_bind_swap]
  simp only [probEvent_eq_eq_probOutput]
  refine probOutput_bind_congr' ($ᵗ Bool) true ?_
  intro b; cases b <;> simp [securityExpFixedBit]

/-- The security advantage decomposes into the difference of the two fixed-bit
branch probabilities: `Pr[win] - 1/2 = (Pr[real=1] - Pr[rand=1]) / 2`. -/
lemma securityExp_toReal_sub_half [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : SecurityAdversary St Rho I) (gp : GameParams) :
    (Pr[= true | securityExp cka adversary gp]).toReal - 1 / 2 =
    ((Pr[= true | securityExpFixedBit cka adversary true gp]).toReal -
     (Pr[= true | securityExpFixedBit cka adversary false gp]).toReal) / 2 := by
  rw [show (Pr[= true | securityExp cka adversary gp]).toReal =
      (Pr[= true | do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let z ← if b then securityExpFixedBit cka adversary true gp
                 else securityExpFixedBit cka adversary false gp
        pure (b == z)]).toReal from by
    congr 1; exact securityExp_probOutput_eq_branch cka adversary gp]
  exact probOutput_uniformBool_branch_toReal_sub_half
    (securityExpFixedBit cka adversary true gp)
    (securityExpFixedBit cka adversary false gp)

/-- CKA security advantage: `|Pr[Win] - 1/2|`. -/
noncomputable def securityAdvantage [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho) (adversary : SecurityAdversary St Rho I)
    (gp : GameParams) : ℝ :=
  |(Pr[= true | securityExp cka adversary gp]).toReal - 1 / 2|

end Games

end CKAScheme

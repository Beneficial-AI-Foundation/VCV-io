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
structure CKAScheme (m : Type → Type u) (IK St I Rho : Type)
    extends ExecutionMethod m where
  initKeyGen : m IK
  initA : IK → m St
  initB : IK → m St
  sendA : St → m (I × Rho × St)
  recvA : St → Rho → (Option I × St)
  sendB : St → m (I × Rho × St)
  recvB : St → Rho → (Option I × St)

namespace CKAScheme

variable {m : Type → Type v} {IK St I Rho : Type}
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
- **TODO:** corruption oracles.

As in [TripleRatchet, SPQR], and contrary to [ACD19], we don't consider additional oracles that
allow to corrupt the randomness of a sending party.

As in [ACD19,TripleRathet], and contrary to [SPQR], we consider *Alternating Communication*:
the games enforce parties A and B to execute the sending and receiving
algorithms in an alternating order.

As in [ACD19, TripleRatchet], and contrary to [SPQR], we have a *fully Passive Adversary*:
it can neither modify nor reorder sent messages.

We define two games sharing the same oracles:
- **Correctness game**: adversary wins if receiver and sender keys don't agree.
- **Security game**: adversary wind if it can distinguish a real from a random key.

-/

section Games

variable {IK St I Rho : Type}

/-- Trace of protocol actions observed in the CKA game. -/
inductive CKAAction where
  | sendA | recvA | sendB | recvB | challA | challB
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

/-- Internal state of the CKA game:
`(stA, stB, ρA, ρB, kA, kB, b, correct, lastAction)`. -/
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

/-- Oracle spec for the CKA correctness game (send + recv only). -/
def ckaCorrectnessSpec (Rho I : Type) :=
  unifSpec                        -- Uniform randomness
  + (Unit →ₒ Option (Rho × I))   -- O-Send-A
  + (Unit →ₒ Unit)               -- O-Recv-A
  + (Unit →ₒ Option (Rho × I))   -- O-Send-B
  + (Unit →ₒ Unit)               -- O-Recv-B

/-- Oracle spec for the CKA security game (send + recv + challenge). -/
def ckaSecuritySpec (Rho I : Type) :=
  ckaCorrectnessSpec Rho I
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-A
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-B

/-! ### Send oracles -/

/-- `O-Send-A`: `(I, ρ, stA') ← sendA(stA); return (ρ, I)`. -/
def oracleSendA (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get -- game state
    if validStep state.lastAction .sendA then -- alternate communication
      let (key, ρ, stA') ← liftM (cka.sendA state.stA) -- send message
      set { state with -- update game state
        stA := stA'
        lastRhoA := some ρ
        lastKeyA := some key
        lastAction := some .sendA }
      return some (ρ, key) -- return message and key
    else pure none

/-- `O-Send-B`: `(I, ρ, stB') ← sendB(stB); return (ρ, I)`. -/
def oracleSendB (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get -- game state
    if validStep state.lastAction .sendB then -- alternate communication
      let (key, ρ, stB') ← liftM (cka.sendB state.stB) -- send message
      set { state with -- update game state
        stB := stB'
        lastRhoB := some ρ
        lastKeyB := some key
        lastAction := some .sendB }
      return some (ρ, key) -- return message and key
    else pure none

/-! ### Receive oracles -/

/-- `O-Recv-A`: deliver pending `ρ` from B; `(I, stA') ← recvA(stA, ρ); assert I = Iᴮ`. -/
def oracleRecvA [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get -- game state
    if validStep state.lastAction .recvA then -- alternate communication
      match state.lastRhoB with
      | none => pure () -- no pending message
      | some ρ =>
        let (keyA, stA') := cka.recvA state.stA ρ -- receive message
        let ok := match state.lastKeyB with
          | some keyB => decide (keyA = some keyB)
          | none => false
        set { state with -- update game state
          stA := stA'
          lastRhoB := none
          lastKeyB := none
          correct := state.correct && ok -- assert key agreement
          lastAction := some .recvA }
    else pure ()

/-- `O-Recv-B`: deliver pending `ρ` from A; `(I, stB') ← recvB(stB, ρ); assert I = Iᴬ`. -/
def oracleRecvB [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get -- game state
    if validStep state.lastAction .recvB then -- alternate communication
      match state.lastRhoA with
      | none => pure () -- no pending message
      | some ρ =>
        let (keyB, stB') := cka.recvB state.stB ρ -- receive message
        let ok := match state.lastKeyA with
          | some keyA => decide (keyB = some keyA)
          | none => false
        set { state with -- update game state
          stB := stB'
          lastRhoA := none
          lastKeyA := none
          correct := state.correct && ok -- assert key agreement
          lastAction := some .recvB }
    else pure ()

/-! ### Challenge oracles -/

/-- `O-Chall-A`: like `O-Send-A` but `return (ρ, b ? $I : I)`. -/
def oracleChallA [SampleableType I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get -- game state
    if validStep state.lastAction .challA then -- alternate communication
      let (key, ρ, stA') ← liftM (cka.sendA state.stA)
      -- return real key or random key
      let outKey ← if state.b then liftM ($ᵗ I : ProbComp I) else pure key
      set { state with -- update game state
        stA := stA'
        lastRhoA := some ρ
        lastKeyA := some key
        lastAction := some .challA }
      return some (ρ, outKey) -- return message and key
    else pure none

/-- `O-Chall-B`: like `O-Send-B` but `return (ρ, b ? $I : I)`. -/
def oracleChallB [SampleableType I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get -- game state
    if validStep state.lastAction .challB then -- alternate communication
      let (key, ρ, stB') ← liftM (cka.sendB state.stB) -- send message
      -- return real key or random key
      let outKey ← if state.b then liftM ($ᵗ I : ProbComp I) else pure key
      set { state with -- update game state
        stB := stB'
        lastRhoB := some ρ
        lastKeyB := some key
        lastAction := some .challB }
      return some (ρ, outKey) -- return message and key
    else pure none

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
def ckaSecurityImpl [SampleableType I] [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (ckaSecuritySpec Rho I) (StateT (GameState St I Rho) ProbComp) :=
  ckaCorrectnessImpl cka
    + oracleChallA cka + oracleChallB cka

/-- Correctness adversary: send + recv oracles only. -/
abbrev CorrectnessAdversary (Rho I : Type) := OracleComp (ckaCorrectnessSpec Rho I) Bool

/-- Security adversary: send + recv + challenge oracles. -/
abbrev SecurityAdversary (Rho I : Type) := OracleComp (ckaSecuritySpec Rho I) Bool

/-! ### Correctness game -/

def correctnessExp [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CorrectnessAdversary Rho I) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let initState : GameState St I Rho :=
    ⟨stA, stB, none, none, none, none, false, true, none⟩
  let (_, state) ← (simulateQ (ckaCorrectnessImpl cka) adversary).run initState
  return state.correct

/-! ### Security game -/

def securityExp [SampleableType I] [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : SecurityAdversary Rho I) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let b ← $ᵗ Bool
  let initState : GameState St I Rho :=
    ⟨stA, stB, none, none, none, none, b, true, none⟩
  let (b', _) ← (simulateQ (ckaSecurityImpl cka) adversary).run initState
  return (b == b')

/-- CKA security advantage: `|Pr[Win] - 1/2|`. -/
noncomputable def securityAdvantage [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho) (adversary : SecurityAdversary Rho I) : ℝ :=
  |(Pr[= true | securityExp cka adversary]).toReal - 1 / 2|

end Games

end CKAScheme

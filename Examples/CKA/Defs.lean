import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.PreservesInv

/-!
# Continuous Key Agreement (CKA)

A CKA is a two-party stateful protocol where two parties A and B take turns exchanging
protocol messages. Every send/receive pair yields a fresh shared epoch key.
Formally, a `CKAScheme` is a set of algorithms over

[SPACES]
- `IK`: initial shared key material,
- `St`: per-party local state.
- `I`: epoch-key space.
- `Rho`: protocol-message space.

[ALGORITHMS]
- `initKeyGen() → ik`
  samples the initial key material `ik : IK` shared before the first protocol
  message.
  [LEAN]: `initKeyGen : m IK`.
- `initA(ik) → stA₀`
  initializes A's local state `stA₀ : St` from `ik`.
  [LEAN]: `initA : IK → m St`.
- `initB(ik) → stB₀`
  initializes B's local state `stB₀ : St` from the same `ik`.
  [LEAN]: `initB : IK → m St`.
- `sendA(stA) → (kA, ρA, stA')`
  A derives an epoch key `kA : I`, sends message `ρA : Rho` to B, and moves to
  state `stA' : St`.
  [LEAN]: `sendA : St → m (Option (I × Rho × St))`.
- `recvA(stA, ρB) → (kA, stA')`
  A receives B's message `ρB`, derives the matching epoch key `kA : I`, and
  updates to `stA' : St`.
  [LEAN]: `recvA : St → Rho → Option (I × St)`.
- `sendB(stB) → (kB, ρB, stB')`
  B derives an epoch key `kB : I`, sends message `ρB : Rho` to A, and moves to
  state `stB' : St`.
  [LEAN]: `sendB : St → m (Option (I × Rho × St))`.
- `recvB(stB, ρA) → (kB, stB')`
  B receives A's message `ρA`, derives the matching epoch key `kB : I`, and
  updates to `stB' : St`.
  [LEAN]: `recvB : St → Rho → Option (I × St)`.


[DIAGRAMS]
```text
Setup:

  initKeyGen() ──▶ ik
                   │
          ┌────────┴────────┐
          ▼                 ▼
      initA(ik)          initB(ik)
          │                 │
          ▼                 ▼
        stA₀              stB₀

Alternating protocol flow:

A state stA                         B state stB
───────────                         ───────────
sendA(stA) ──▶ (kA, ρA, stA')
                      │
                      │ ρA
                      ▼
                 recvB(stB, ρA)  ──▶ (kB, stB')

[CORRECTNESS: kA =?= kB]
[NEXT ROUND]
                (kB', ρB, stB'') ◀── sendB(stB')         │
                      │
                      │ ρB
                      ▼
(kA', stA'') ◀── recvA(stA', ρB)
[CORRECTNESS: kA' =?= kB']
```


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
  -- samples initial shared key
  initKeyGen : m IK
  -- initializes A's local state from the initial key
  initA : IK → m St
  -- initializes B's local state from the initial key
  initB : IK → m St
  -- Party A's send: returns the fresh epoch key, message sent to B, and A's next state.
  sendA : St → m (Option (I × Rho × St))
  -- Party A's receive: returns the derived epoch key and A's next state.
  recvA : St → Rho → Option (I × St)
  -- Party B's send: returns the fresh epoch key, message sent to A, and B's next state.
  sendB : St → m (Option (I × Rho × St))
  -- Party B's receive: returns the derived epoch key and B's next state.
  recvB : St → Rho → Option (I × St)

namespace CKAScheme

variable {m : Type → Type v} [Monad m] {IK St I Rho : Type}
  (cka : CKAScheme m IK St I Rho)


/-! ## Security Model

As in [ACD19, TripleRatchet], and contrary to [SPQR], we assume the following:

- **Alternating Communication**: parties A and B execute the sending and
receiving algorithms in an alternating order.

- **Fully Passive Adversary**: the adversary can neither modify nor reorder sent messages.

- **Static Challenge Epoch**: the security adversary can only challenge the key for one epoch,
which is fixed at the beginning of the security experiment.

As in [TripleRatchet, SPQR], and contrary to [ACD19], we don't consider oracles that
allow to corrupt the randomness of a sending party.

These assumptions are enforced by checks in the oracles defining the CKA security game.
The oracles are:
- **O-Send-A / O-Send-B**
  Trigger one party to send, return `(ρ, key)`, and update the sender state.
- **O-Recv-A / O-Recv-B**
  Deliver the latest message in that direction and update the receiver state.
  *Correctness assert*: the received key must match the sender's corresponding key.
- **O-Chall-A / O-Chall-B**
  Like send, but return real key (`b = 0`) or random key (`b = 1`).
- **O-Corrupt-A / O-Corrupt-B**
  Return the current state of party A (resp. B) and record the corruption epoch.

We define two games:
- **Correctness game**: adversary wins if there is an epoch where the receiver
  and sender keys don't match.
- **Security game**: adversary wins if it can distinguish a real from a random
  key at the challenge epoch.

-/

section Games

variable {IK St I Rho : Type}

/-- Trace of protocol actions observed in the CKA game. -/
inductive CKAAction where
  | sendA | recvA | sendB | recvB | challA | challB
  deriving DecidableEq, Repr

/-- The two parties in a CKA protocol. -/
inductive CKAParty where
  | A | B
  deriving DecidableEq, Repr

/-- The opposite party: `A.other = B` and `B.other = A`. -/
def CKAParty.other : CKAParty → CKAParty
  | .A => .B
  | .B => .A

/-- Predicate enforcing *Alternating Communication*.

The game is A-first and follows the cycle
`A-send/chall → B-recv → B-send/chall → A-recv → A-send/chall → ...`.
Challenge steps run the sending algorithm but return a real-or-random key to
the adversary. -/
def validStep (last : Option CKAAction) (next : CKAAction) : Bool :=
  match last, next with
  -- The first action must be an A-side send or challenge.
  | none, .sendA | none, .challA => true
  -- After A sends, B must receive A's message.
  | some .sendA, .recvB | some .challA, .recvB => true
  -- After B receives, B may send or challenge.
  | some .recvB, .sendB | some .recvB, .challB => true
  -- After B sends, A must receive B's message.
  | some .sendB, .recvA | some .challB, .recvA => true
  -- After A receives, the next round starts with an A-side send or challenge.
  | some .recvA, .sendA | some .recvA, .challA => true
  | _, _ => false

/-- Game parameters fixed at the start of the security experiment. -/
structure GameParams where
  tStar : ℕ              -- epoch that adversary will challenge
  deltaCKA : ℕ           -- healing delay after state corruption
  challengedParty : CKAParty  -- which party `P ∈ {A, B}` is challenged

/-- Internal state of the CKA game.
- `stA`, `stB`: per-party protocol state.
- `rhoA/B`, `keyA/B`: pending undelivered message and sender key.
- `b`: hidden challenge bit (security game only).
- `correct`: conjunction of all key-agreement checks so far.
- `lastAction`: enforces alternating communication.
- `tA`, `tB`: epoch counters (incremented on each send/chall/recv). -/
structure GameState (St I Rho : Type) where
  stA : St
  stB : St
  rhoA : Option Rho  -- latest undelivered A -> B message
  rhoB : Option Rho  -- latest undelivered B -> A message
  keyA : Option I    -- sender key paired with `rhoA`
  keyB : Option I    -- sender key paired with `rhoB`
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

/-- Oracle spec for the CKA correctness game (send + recv only).
Defines the expected oracles types. -/
def ckaCorrectnessSpec (Rho I : Type) :=
  unifSpec                        -- Uniform randomness
  + (Unit →ₒ Option (Rho × I))   -- O-Send-A (outputs message and key)
  + (Unit →ₒ Unit)               -- O-Recv-A (no I/O)
  + (Unit →ₒ Option (Rho × I))   -- O-Send-B (outputs message and key)
  + (Unit →ₒ Unit)               -- O-Recv-B (no I/O)

/-- Oracle spec for the CKA security game (send + recv + challenge + corrupt).
Defines the expected oracles types. -/
def ckaSecuritySpec (St Rho I : Type) :=
  ckaCorrectnessSpec Rho I
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-A (outputs message and key)
  + (Unit →ₒ Option (Rho × I))   -- O-Chall-B (outputs message and key)
  + (Unit →ₒ Option St)           -- O-Corrupt-A (outputs party state)
  + (Unit →ₒ Option St)           -- O-Corrupt-B (outputs party state)

namespace ckaSecuritySpec

variable {St Rho I : Type}

/-! ### Named oracle indices

Aliases for the nested `.inl/.inr` paths into `(ckaSecuritySpec St Rho I).Domain`.
Marked `@[match_pattern]` so they unfold transparently in `match` patterns. -/
@[match_pattern] abbrev OUnif (n : ℕ) : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl n)))))))
@[match_pattern] abbrev OSendA : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr ())))))))
@[match_pattern] abbrev ORecvA : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inr ()))))))
@[match_pattern] abbrev OSendB : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inl (.inl (.inl (.inl (.inr ())))))
@[match_pattern] abbrev ORecvB : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inl (.inl (.inl (.inr ()))))
@[match_pattern] abbrev OChallA : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inl (.inl (.inr ())))
@[match_pattern] abbrev OChallB : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inl (.inr ()))
@[match_pattern] abbrev OCorruptA : (ckaSecuritySpec St Rho I).Domain :=
  .inl (.inr ())
@[match_pattern] abbrev OCorruptB : (ckaSecuritySpec St Rho I).Domain :=
  .inr ()

end ckaSecuritySpec

/-! ### Epoch predicates -/

/-- Challenge fires when the challenged party's counter reaches `tStar`. -/
def isChallengeEpoch (gp : GameParams) (state : GameState St I Rho) : Bool :=
  state.tP gp.challengedParty == gp.tStar

/-- The opposite party is sending in the epoch immediately before the challenge.

If party `P = gp.challengedParty` is challenged at epoch `tStar`, this predicate
recognizes the send by the opposite party at epoch `tStar - 1`. -/
def isOtherSendBeforeChall (gp : GameParams) (state : GameState St I Rho) : Bool :=
  state.tP gp.challengedParty.other == gp.tStar - 1

/-- Determines if party A has healed: `tA ≥ t* + ΔCKA`. -/
abbrev finishedA (gp : GameParams) (state : GameState St I Rho) : Bool :=
  gp.tStar + gp.deltaCKA ≤ state.tA

/-- Determines if party B has healed: `tB ≥ t* + ΔCKA`. -/
abbrev finishedB (gp : GameParams) (state : GameState St I Rho) : Bool :=
  gp.tStar + gp.deltaCKA ≤ state.tB

/-- Corruption allowed before the challenge window: `(max tA tB) + 2 ≤ tStar`. -/
def allowCorr (gp : GameParams) (state : GameState St I Rho) : Bool :=
  (max state.tA state.tB) + 2 ≤ gp.tStar

/-! ### Send oracles -/

/-- **O-Send-A.**
Increment epoch counter, trigger send by A, return message and key.
`tA++; (key, ρ, stA') ← sendA(stA)`; return `(ρ, key)`. -/
def oracleSendA (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow A to send if it is A's turn in alternating communication.
    if validStep state.lastAction .sendA then
      -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
      -- Run A's send algorithm on the current A-state.
      match ← liftM (cka.sendA state.stA) with
      | none => pure none
      | some (key, ρ, stA') =>
        -- Update game state.
        set { state with
          stA := stA', rhoA := some ρ, keyA := some key,
          lastAction := some .sendA }
        -- Return the message and key to the adversary.
        return some (ρ, key)
    else pure none

/-- **O-Send-B.**
Increment epoch counter, trigger send by B, return message and key.
`tB++; (key, ρ, stB') ← sendB(stB)`; return `(ρ, key)`. -/
def oracleSendB (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    -- Only allow B to send if it is B's turn in alternating communication.
    if validStep state.lastAction .sendB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      -- Run B's send algorithm on the current B-state.
      match ← liftM (cka.sendB state.stB) with
      | none => pure none
      | some (key, ρ, stB') =>
        -- Update game state.
        set { state with
          stB := stB', rhoB := some ρ, keyB := some key,
          lastAction := some .sendB }
        -- Return the message and key to the adversary.
        return some (ρ, key)
    else pure none

/-! ### Receive oracles -/

/-- **O-Recv-A.**
Increment epoch counter, deliver B's message to A, return key and A's next state.
`tA++; (keyA, stA') ← recvA(stA, ρB)`; assert `keyA = keyB`. -/
def oracleRecvA [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .recvA then
      -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
      match state.rhoB with
      | none => pure ()
      | some ρ =>
        -- Run A's receive algorithm on the current A-state and B's message.
        match cka.recvA state.stA ρ with
        | none => pure ()
        | some (keyA, stA') =>
          let ok := match state.keyB with
           -- correct if keyA == keyB
            | some keyB => decide (some keyA = some keyB)
            | none => false
          set { state with
            -- Update game state.
            stA := stA', rhoB := none, keyB := none,
            -- Update correctness flag.
            correct := state.correct && ok, lastAction := some .recvA }
    else pure ()

/-- **O-Recv-B.**
Increment epoch counter, deliver A's message to B, return key and B's next state.
`tB++; (keyB, stB') ← recvB(stB, ρA)`; assert `keyB = keyA`. -/
def oracleRecvB [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Unit) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .recvB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      match state.rhoA with
      | none => pure ()
      | some ρ =>
        -- Run B's receive algorithm on the current B-state and A's message.
        match cka.recvB state.stB ρ with
        | none => pure ()
        | some (keyB, stB') =>
          let ok := match state.keyA with
            | some keyA => decide (some keyB = some keyA)
            | none => false
          set { state with
            -- Update game state.
            stB := stB', rhoA := none, keyA := none,
            -- Update correctness flag.
            correct := state.correct && ok, lastAction := some .recvB }
    else pure ()

/-! ### Challenge oracles -/

/-- **O-Chall-A.**
Increment epoch counter, trigger send by A, return message and key.
Like `O-Send-A` but returns `b ? $ᵗ I : key` (real or
random key). Only fires when `P = A` and `tA = t*`. -/
def oracleChallA (gp : GameParams) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challA then
    -- Increment A's epoch counter.
      let state := { state with tA := state.tA + 1 }
    -- Enforce correct challenge party and epoch.
      if gp.challengedParty == .A && isChallengeEpoch gp state then
        -- Run A's send algorithm on the current A-state.
        match ← liftM (cka.sendA state.stA) with
        | none => pure none
        | some (key, ρ, stA') =>
          -- Real or random key for the adversary.
          let outKey ← if state.b then liftM ($ᵗ I : ProbComp I) else pure key
          -- Update game state.
          set { state with
            stA := stA', rhoA := some ρ, keyA := some key,
            lastAction := some .challA }
          -- Return the message and key to the adversary.
          return some (ρ, outKey)
      else pure none
    else pure none

/-- **O-Chall-B.**
Increment epoch counter, trigger send by B, return message and key.
Like `O-Send-B` but returns `b ? $ᵗ I : key` (real or
random key). Only fires when `P = A` and `tA = t*`. -/
def oracleChallB (gp : GameParams) [SampleableType I]
    (cka : CKAScheme ProbComp IK St I Rho) :
    QueryImpl (Unit →ₒ Option (Rho × I)) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if validStep state.lastAction .challB then
      -- Increment B's epoch counter.
      let state := { state with tB := state.tB + 1 }
      -- Enforce correct challenge party and epoch.
      if gp.challengedParty == .B && isChallengeEpoch gp state then
        -- Run B's send algorithm on the current B-state.
        match ← liftM (cka.sendB state.stB) with
        | none => pure none
        | some (key, ρ, stB') =>
          let outKey ← if state.b then liftM ($ᵗ I : ProbComp I) else pure key
          -- Update game state.
          set { state with
            stB := stB', rhoB := some ρ, keyB := some key,
            lastAction := some .challB }
          -- Return the message and key to the adversary.
          return some (ρ, outKey)
      else pure none
    else pure none

/-! ### Corruption oracles

Following [ACD19, Def. 13, Fig. 3], corruption is allowed iff
`allowCorr ∨ finishedA` for A, and iff `allowCorr ∨ finishedB` for B.
-/

/-- **O-Corrupt-A.** Return `stA` if `allowCorr ∨ finishedA`. -/
def oracleCorruptA (gp : GameParams) (St I Rho : Type) :
    QueryImpl (Unit →ₒ Option St) (StateT (GameState St I Rho) ProbComp) :=
  fun () => do
    let state ← get
    if allowCorr gp state || finishedA gp state then return some state.stA
    else return none

/-- **O-Corrupt-B.** Return `stB` if `allowCorr ∨ finishedB`. -/
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
abbrev CKACorrectnessAdversary (Rho I : Type) := OracleComp (ckaCorrectnessSpec Rho I) Bool

/-- Security adversary: send + recv + challenge + corruption oracles. -/
abbrev CKAAdversary (St Rho I : Type) := OracleComp (ckaSecuritySpec St Rho I) Bool

/-! ### Correctness game -/

/-- Game state with initial `stA`, `stB`, challenge bit `b`, initial epochs,
and no pending keys or messages. -/
def initGameState (stA stB : St) (b : Bool) : GameState St I Rho :=
  { stA, stB, rhoA := none, rhoB := none,
    keyA := none, keyB := none,
    b, correct := true, lastAction := none,
    tA := 0, tB := 0 }

/-- Correctness experiment:
`ik ← initKeyGen`; `stA ← initA ik`; `stB ← initB ik`; run the adversary from
`initGameState stA stB false`; return the final `state.correct` flag. -/
def correctnessExp [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CKACorrectnessAdversary Rho I) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let (_, state) ←
    (simulateQ (ckaCorrectnessImpl cka) adversary).run (initGameState stA stB false)
  return state.correct

/-! ### Security game -/

/-- Security game as in [ACD19, Def. 13, Fig. 3]:
`ik ← initKeyGen`; `stA ← initA ik`; `stB ← initB ik`; `b ← $ᵗ Bool`;
run the adversary from `initGameState stA stB b`; return `b == b'`. -/
def securityExp [SampleableType I] [DecidableEq I] (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CKAAdversary St Rho I)
    (gp : GameParams) : ProbComp Bool := do
  let ik ← cka.initKeyGen
  let stA ← cka.initA ik
  let stB ← cka.initB ik
  let b ← $ᵗ Bool
  let (b', _) ← (simulateQ (ckaSecurityImpl gp cka) adversary).run (initGameState stA stB b)
  return (b == b')

/-- CKA security advantage: `|Pr[Win] - 1/2|`. -/
noncomputable def securityAdvantage [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho) (adversary : CKAAdversary St Rho I)
    (gp : GameParams) : ℝ :=
  |(Pr[= true | securityExp cka adversary gp]).toReal - 1 / 2|

/-! ### Useful security game decomposition -/

/-- Security game with a fixed challenge bit `b` (not sampled uniformly).
Returns the adversary's raw guess `b'` (not `b == b'`). -/
def securityExpFixedBit [SampleableType I] [DecidableEq I]
    (cka : CKAScheme ProbComp IK St I Rho)
    (adversary : CKAAdversary St Rho I)
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
    (adversary : CKAAdversary St Rho I) (gp : GameParams) :
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
    (adversary : CKAAdversary St Rho I) (gp : GameParams) :
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

end Games

end CKAScheme

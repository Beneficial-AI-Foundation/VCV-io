/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Security
import DoubleRatchet.CKA.MultiEpochGame
import DoubleRatchet.CKA.Figure3Game
import DoubleRatchet.Constructions.DDHCKA
import DoubleRatchet.Theorems.Reduction

/-!
# Theorem 3: DDH Security Implies CKA Security

Theorem 3 from Alwen-Coretti-Dodis (2020), Section 4.1.2, page 22.

**Statement**: If group G is (t,ε)-DDH-secure, then the DDH-based CKA scheme
is (t,Δ,ε)-secure for t ≈ t' and Δ = 1.

This file contains two layers of the theorem:

## Layer 1: Single-epoch warmup

A simple single-epoch reduction showing DDH hardness implies CKA security in
a one-shot game. The DDH adversary `ckaAdvToDDHAdv` receives `(g, aG, bG, cG)`
and forwards `(bG, cG)` directly to the CKA adversary:

- `ckaRealExp_eq_ddhExpReal` / `ckaRandExp_eq_ddhExpRand` — distribution equality
- `ddh_implies_cka_security` — concrete per-adversary bound
- `ddh_implies_cka_security_single_epoch` — epsilon-form warmup wrapper
- `ddh_implies_cka_security_delta` — restricted multi-epoch auxiliary form

## Layer 2: Figure 3 adaptive theorem surface

The paper-faithful statement over the full Figure 3 oracle game with adaptive
interaction, party-specific corruption, and bad-randomness oracles. The
reduction logic lives in `Theorems/Reduction.lean`; this file only states the
theorem:

- `figure3Advantage_le_ddhAdvantage` — helper two-game Figure 3 bound
- `figure3GuessAdvantage_le_ddhAdvantage` — paper-facing hidden-bit Figure 3 bound
- `ddh_implies_figure3_cka_security_two_game` — auxiliary two-game wrapper
- `ddh_implies_figure3_cka_security` — paper-faithful Theorem 3

For the asymptotic wrapper, see `Theorems/AsymptoticSecurity.lean`.

## Why `F`, `Module F G`, and `Function.Bijective (· • g)`?

The type-class `[Module F G]` says "F acts on G by scalar multiplication".
The hypothesis `hg : Function.Bijective (· • g : F → G)` encodes that
G ≅ F as an F-module via `a ↦ a • g` — i.e., G = ⟨g⟩ is cyclic of prime
order |F|. Needed for `ckaRandExp_eq_ddhExpRand`: the CKA random game samples
from G directly, while the DDH random game samples `c ← F` and computes
`c • g`. These are the same distribution iff `(· • g)` is bijective.
-/

set_option autoImplicit false

open OracleComp DiffieHellman

namespace CKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

/-- Given a CKA adversary, construct a DDH adversary with the same advantage.
The DDH adversary ignores `g` and `a • g` (the setup), and feeds
`(b • g, c • g)` = `(T, I_candidate)` to the CKA adversary. -/
def ckaAdvToDDHAdv (adversary : CKAAdversary G G) : DDHAdversary F G :=
  fun _g _aG bG cG => adversary bG cG

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType G] [DecidableEq G] [Inhabited G] in
/-- The CKA real game with the DDH-CKA scheme produces the same distribution
as the DDH real game with the reduced adversary.

CKA real: sample `k ← F`, `x ← F`, adversary sees `(x • g, x • (k • g))`.
DDH real: sample `a ← F`, `b ← F`, adversary sees `(b • g, (a * b) • g)`.
These are identical (with `k = a`, `x = b` and using `smul_smul`). -/
lemma ckaRealExp_eq_ddhExpReal (g : G) (adversary : CKAAdversary G G) :
    ckaRealExp (SharedKey := F) (SenderState := G) (ReceiverState := F)
      (ddhCKA (F := F) g) adversary =
      ddhExpReal (F := F) g (ckaAdvToDDHAdv adversary) := by
  simp [ckaRealExp, ddhExpReal, ckaAdvToDDHAdv, ddhCKA, smul_smul, mul_comm]

omit [DecidableEq F] [Inhabited F] [DecidableEq G] [Inhabited G] in
/-- The CKA random game with the DDH-CKA scheme produces the same distribution
as the DDH random game with the reduced adversary.

Requires `hg : Function.Bijective (· • g)` (i.e., g generates G): the CKA
random game samples uniformly from `G` via `$ᵗ G`, while the DDH random game
samples `c ← $ᵗ F` and computes `c • g`. These distributions coincide iff
`(· • g : F → G)` is bijective. -/
lemma ckaRandExp_eq_ddhExpRand (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (adversary : CKAAdversary G G) :
    evalDist (ckaRandExp (SharedKey := F) (SenderState := G) (ReceiverState := F)
      (ddhCKA (F := F) g) adversary) =
      evalDist (ddhExpRand (F := F) g (ckaAdvToDDHAdv adversary)) := by
  apply evalDist_ext
  intro z
  simp [ckaRandExp, ddhExpRand, ckaAdvToDDHAdv, ddhCKA]
  refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
  intro a
  symm
  exact probOutput_bind_bijective_uniform_cross
    (α := F) (β := G) (fun c : F => c • g) hg
    (fun randOutput : G => adversary (a • g) randOutput) z

omit [DecidableEq F] [Inhabited F] [DecidableEq G] [Inhabited G] in
/-- **Theorem 3** (Alwen-Coretti-Dodis 2020), concrete per-adversary form:

For every CKA adversary `A`, its advantage against the DDH-CKA scheme is
bounded by the DDH advantage of the reduced adversary `ckaAdvToDDHAdv A`.

The hypothesis `hg` formalizes "G = ⟨g⟩ is cyclic of prime order |F|".
See the module docstring for why this is needed and how it relates to the
standard mathematical definition of a cyclic group. -/
theorem ddh_implies_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (adversary : CKAAdversary G G) :
    ckaDistAdvantage (ddhCKA (F := F) g) adversary ≤
      ddhDistAdvantage (F := F) g (ckaAdvToDDHAdv adversary) := by
  unfold ckaDistAdvantage ddhDistAdvantage
  rw [ckaRealExp_eq_ddhExpReal g adversary]
  have hrand :
      Pr[= true | ckaRandExp (SharedKey := F) (SenderState := G) (ReceiverState := F)
        (ddhCKA (F := F) g) adversary] =
        Pr[= true | ddhExpRand (F := F) g (ckaAdvToDDHAdv adversary)] :=
    probOutput_congr rfl (ckaRandExp_eq_ddhExpRand g hg adversary)
  rw [hrand]

omit [DecidableEq F] [Inhabited F] [DecidableEq G] [Inhabited G] in
/-- **Theorem 3** (Alwen-Coretti-Dodis 2020), single-epoch epsilon form:

If every DDH adversary has advantage ≤ ε, then every single-epoch CKA
adversary has advantage ≤ ε. This follows from `ddh_implies_cka_security`
by instantiation.

**Note**: This targets `CKASecure` (single-epoch game), not the full
Figure 3 adaptive game. For the paper-faithful Figure 3 statement, see
`ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_cka_security_single_epoch (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    CKASecure (ddhCKA (F := F) g) ε := by
  intro adversary
  exact le_trans (ddh_implies_cka_security g hg adversary) (hDDH _)

omit [Fintype F] [DecidableEq F] [Inhabited F] [DecidableEq G] [Inhabited G] in
/-- Package a pointwise reduction from restricted multi-epoch CKA adversaries to
DDH adversaries into `CKASecureDelta`.

The simulation proof is supplied as `hreduce`; this lemma only performs the
advantage transitivity step against the DDH security hypothesis. -/
lemma CKASecureDelta_of_reduction (g : G) (ε : ℝ)
    (reduce : MultiEpochCKAAdversary G G G F → DDHAdversary F G)
    (hreduce : ∀ A : MultiEpochCKAAdversary G G G F,
      multiEpochAdvantage (ddhCKA (F := F) g) 1 A ≤
        ddhDistAdvantage (F := F) g (reduce A))
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    CKASecureDelta (ddhCKA (F := F) g) 1 ε := by
  intro A
  exact le_trans (hreduce A) (hDDH (reduce A))

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- Direct DDH simulation of the restricted multi-epoch transcript game.

The simulator carries the previous epoch's public state and, when known, the
matching scalar. At the two hidden epochs around `tStar`, it embeds the DDH
tuple:

- epoch `tStar - 1`: message `aG`;
- epoch `tStar`: message `bG`, candidate output `cG`.

The stored sender state at hidden epochs uses `default`. For `delta = 1`,
those epochs are never revealed by `computeRevealedStates`; the lemmas below
record the corresponding corruption-window facts. -/
def ddhMultiEpochSimRun (g aG bG cG : G) (tStar currentEpoch : ℕ) :
    (remaining : ℕ) → Option F → G → ProbComp (EpochResult G G G F)
  | 0, prevSecret, prevPub =>
      pure ⟨[], [], prevPub, prevSecret.getD default⟩
  | n + 1, prevSecret, prevPub => do
      let (nextSecret, msg, output, storedSecret) ←
        if currentEpoch + 1 = tStar then
          pure (none, aG,
            match prevSecret with
            | some x => x • aG
            | none => default,
            default)
        else if currentEpoch = tStar then
          pure (none, bG, cG, default)
        else do
          let x ← $ᵗ F
          pure (some x, x • g, x • prevPub, x)
      let rest ← ddhMultiEpochSimRun g aG bG cG tStar (currentEpoch + 1) n nextSecret msg
      pure ⟨(msg, output) :: rest.transcript,
        Sum.inr storedSecret :: rest.senderStatesAfter,
        rest.finalSender,
        rest.finalReceiver⟩

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- Reduction from restricted multi-epoch CKA adversaries to DDH adversaries.

When `A.tStar = 1`, the DDH value `aG` is embedded as the initial public
state. Otherwise the simulator samples the honest initial scalar and embeds
`aG` at epoch `tStar - 1`. -/
def multiEpochAdvToDDHAdv
    (A : MultiEpochCKAAdversary G G G F) : DDHAdversary F G :=
  fun g aG bG cG => do
    let (initSecret, initPub) ←
      if A.tStar = 1 then
        pure (none, aG)
      else do
        let k ← $ᵗ F
        pure (some k, k • g)
    let result ← ddhMultiEpochSimRun (F := F) g aG bG cG A.tStar 1 A.numEpochs
      initSecret initPub
    let revealed := computeRevealedStates result.senderStatesAfter
      A.corruptionRequests A.tStar 1
    A.guess result.transcript revealed

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [Inhabited F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [Inhabited G] in
/-- With `delta = 1`, the epoch immediately before the challenge cannot be revealed. -/
lemma not_corruptionPermitted_pred_tStar_delta_one (tStar : ℕ) (ht : 0 < tStar) :
    ¬ corruptionPermitted (tStar - 1) tStar 1 := by
  unfold corruptionPermitted allowCorr epochFinished
  omega

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [Inhabited F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [Inhabited G] in
/-- With `delta = 1`, the challenge epoch itself cannot be revealed. -/
lemma not_corruptionPermitted_tStar_delta_one (tStar : ℕ) :
    ¬ corruptionPermitted tStar tStar 1 := by
  unfold corruptionPermitted allowCorr epochFinished
  omega

/-- A forbidden epoch contributes no revealed state. -/
lemma filterCorruptionReveals_cons_forbidden
    {SenderState ReceiverState : Type}
    (epoch tStar delta : ℕ) (state : SenderState ⊕ ReceiverState)
    (states : List (ℕ × (SenderState ⊕ ReceiverState)))
    (h : ¬ corruptionPermitted epoch tStar delta) :
    filterCorruptionReveals ((epoch, state) :: states) tStar delta =
      filterCorruptionReveals states tStar delta := by
  simp [filterCorruptionReveals, h]

/-- A permitted epoch contributes its state to the reveal list. -/
lemma filterCorruptionReveals_cons_permitted
    {SenderState ReceiverState : Type}
    (epoch tStar delta : ℕ) (state : SenderState ⊕ ReceiverState)
    (states : List (ℕ × (SenderState ⊕ ReceiverState)))
    (h : corruptionPermitted epoch tStar delta) :
    filterCorruptionReveals ((epoch, state) :: states) tStar delta =
      state :: filterCorruptionReveals states tStar delta := by
  simp [filterCorruptionReveals, h]

/-- Replacing the state at a forbidden indexed epoch does not change the
revealed corruption state list. -/
lemma indexedRevealedStates_replace_forbidden
    {SenderState ReceiverState : Type}
    (start : ℕ) (statePrefix : List (SenderState ⊕ ReceiverState))
    (x y : SenderState ⊕ ReceiverState) (suffix : List (SenderState ⊕ ReceiverState))
    (corruptionRequests : List ℕ) (tStar delta : ℕ)
    (h : ¬ corruptionPermitted (start + statePrefix.length) tStar delta) :
    filterCorruptionReveals
        ((indexFrom start (statePrefix ++ x :: suffix)).filter
          (fun (epoch, _) => decide (epoch ∈ corruptionRequests))) tStar delta =
      filterCorruptionReveals
        ((indexFrom start (statePrefix ++ y :: suffix)).filter
          (fun (epoch, _) => decide (epoch ∈ corruptionRequests))) tStar delta := by
  induction statePrefix generalizing start with
  | nil =>
      have hstart : ¬ corruptionPermitted start tStar delta := by
        simpa using h
      simp [indexFrom, filterCorruptionReveals, hstart]
  | cons p statePrefix ih =>
      have htail : ¬ corruptionPermitted (start + 1 + statePrefix.length) tStar delta := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hih := ih (start + 1) htail
      by_cases hreq : start ∈ corruptionRequests
      · by_cases hperm : corruptionPermitted start tStar delta
        · simpa [indexFrom, filterCorruptionReveals, hreq, hperm] using hih
        · simpa [indexFrom, filterCorruptionReveals, hreq, hperm] using hih
      · simpa [indexFrom, filterCorruptionReveals, hreq] using hih

/-- Specialization of `indexedRevealedStates_replace_forbidden` to
`computeRevealedStates`, whose indexing starts at epoch 1. -/
lemma computeRevealedStates_replace_forbidden
    {SenderState ReceiverState : Type}
    (statePrefix : List (SenderState ⊕ ReceiverState))
    (x y : SenderState ⊕ ReceiverState) (suffix : List (SenderState ⊕ ReceiverState))
    (corruptionRequests : List ℕ) (tStar delta : ℕ)
    (h : ¬ corruptionPermitted (statePrefix.length + 1) tStar delta) :
    computeRevealedStates (statePrefix ++ x :: suffix) corruptionRequests tStar delta =
      computeRevealedStates (statePrefix ++ y :: suffix) corruptionRequests tStar delta := by
  have h' : ¬ corruptionPermitted (1 + statePrefix.length) tStar delta := by
    simpa [Nat.add_comm] using h
  simpa [computeRevealedStates, Nat.add_comm] using
    (indexedRevealedStates_replace_forbidden (start := 1) statePrefix x y suffix
      corruptionRequests tStar delta h')

/-- Rotate three independent probabilistic binds, bringing the third sample to
the front. This is used to align the DDH experiment's sampling order with the
restricted multi-epoch game, whose honest initial key is sampled before epoch
coins. -/
lemma probOutput_bind_bind_bind_rotate
    {α β γ δ : Type} (mx : ProbComp α) (my : ProbComp β) (mz : ProbComp γ)
    (f : α → β → γ → ProbComp δ) (z : δ) :
    Pr[= z | mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c] =
      Pr[= z | mz >>= fun c => mx >>= fun a => my >>= fun b => f a b c] := by
  rw [probOutput_bind_congr' mx z]
  · rw [probOutput_bind_bind_swap]
  intro a
  exact probOutput_bind_bind_swap my mz (fun b c => f a b c) z

/-- Rotate four independent probabilistic binds, bringing the fourth sample to
the front. -/
lemma probOutput_bind_bind_bind_bind_rotate
    {α β γ δ ε : Type} (mx : ProbComp α) (my : ProbComp β) (mz : ProbComp γ)
    (mw : ProbComp δ) (f : α → β → γ → δ → ProbComp ε) (z : ε) :
    Pr[= z | mx >>= fun a => my >>= fun b => mz >>= fun c => mw >>= fun d => f a b c d] =
      Pr[= z | mw >>= fun d => mx >>= fun a => my >>= fun b => mz >>= fun c =>
        f a b c d] := by
  calc
    Pr[= z | mx >>= fun a => my >>= fun b => mz >>= fun c => mw >>= fun d => f a b c d] =
        Pr[= z | mx >>= fun a => mw >>= fun d => my >>= fun b => mz >>= fun c =>
          f a b c d] := by
          rw [probOutput_bind_congr' mx z]
          intro a
          exact probOutput_bind_bind_bind_rotate my mz mw (fun b c d => f a b c d) z
    _ = Pr[= z | mw >>= fun d => mx >>= fun a => my >>= fun b => mz >>= fun c =>
        f a b c d] := by
          exact probOutput_bind_bind_swap mx mw
            (fun a d => my >>= fun b => mz >>= fun c => f a b c d) z

omit [Fintype F] [DecidableEq F] [DecidableEq G] [Inhabited F] [Inhabited G] in
/-- Once the current epoch is past the random challenge epoch, `runEpochsRand`
is definitionally the honest epoch runner. -/
lemma runEpochsRand_after_challenge_eq_runEpochs
    (g : G) (tStar currentEpoch remaining : ℕ) (prevPub : G) (prevSecret : F)
    (hcur : tStar < currentEpoch) :
    runEpochsRand (ddhCKA (F := F) g) tStar currentEpoch remaining prevPub prevSecret =
      runEpochs (ddhCKA (F := F) g) currentEpoch remaining prevPub prevSecret := by
  induction remaining generalizing currentEpoch prevPub prevSecret with
  | zero =>
      simp [runEpochsRand, runEpochs]
  | succ n ih =>
      have hchal : currentEpoch ≠ tStar := by omega
      simp [runEpochsRand, runEpochs, ddhCKA, hchal]
      apply bind_congr
      intro x
      have hcur' : tStar < currentEpoch + 1 := by omega
      change (fun a : EpochResult G G G F =>
          (⟨(x • g, x • prevPub) :: a.transcript,
            Sum.inr x :: a.senderStatesAfter,
            a.finalSender,
            a.finalReceiver⟩ : EpochResult G G G F)) <$>
        runEpochsRand (ddhCKA (F := F) g) tStar (currentEpoch + 1) n (x • g) x =
        (fun a : EpochResult G G G F =>
          (⟨(x • g, x • prevPub) :: a.transcript,
            Sum.inr x :: a.senderStatesAfter,
            a.finalSender,
            a.finalReceiver⟩ : EpochResult G G G F)) <$>
        runEpochs (ddhCKA (F := F) g) (currentEpoch + 1) n (x • g) x
      rw [ih (currentEpoch + 1) (x • g) x hcur']

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- After the `tStar = 1` challenge window, once the simulator carries a known
receiver scalar, the restricted DDH simulator is definitionally the honest
DDH-CKA epoch runner. -/
lemma ddhMultiEpochSimRun_tStar_one_some_eq_runEpochs
    (g aG bG cG prevPub : G) (currentEpoch remaining : ℕ) (prevSecret : F)
    (hcur : 1 < currentEpoch) :
    ddhMultiEpochSimRun (F := F) g aG bG cG 1 currentEpoch remaining
      (some prevSecret) prevPub =
      runEpochs (ddhCKA (F := F) g) currentEpoch remaining prevPub prevSecret := by
  induction remaining generalizing currentEpoch prevSecret prevPub with
  | zero =>
      simp [ddhMultiEpochSimRun, runEpochs]
  | succ n ih =>
      have h0 : currentEpoch ≠ 0 := by omega
      have h1 : currentEpoch ≠ 1 := by omega
      simp [ddhMultiEpochSimRun, runEpochs, ddhCKA, h0, h1]
      apply bind_congr
      intro x
      have hcur' : 1 < currentEpoch + 1 := by omega
      rw [ih (x • g) (currentEpoch + 1) x hcur']
      rfl

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- After `tStar = 1`, if at least one post-challenge epoch remains, that fresh
epoch restores a known scalar and the tail coincides with the honest runner. -/
lemma ddhMultiEpochSimRun_tStar_one_none_succ_eq_runEpochs
    (g aG bG cG prevPub : G) (currentEpoch n : ℕ) (prevSecret : F)
    (hcur : 1 < currentEpoch) :
    ddhMultiEpochSimRun (F := F) g aG bG cG 1 currentEpoch (n + 1) none prevPub =
      runEpochs (ddhCKA (F := F) g) currentEpoch (n + 1) prevPub prevSecret := by
  have h0 : currentEpoch ≠ 0 := by omega
  have h1 : currentEpoch ≠ 1 := by omega
  simp [ddhMultiEpochSimRun, runEpochs, ddhCKA, h0, h1]
  apply bind_congr
  intro x
  have hcur' : 1 < currentEpoch + 1 := by omega
  rw [ddhMultiEpochSimRun_tStar_one_some_eq_runEpochs
    (F := F) g aG bG cG (x • g) (currentEpoch + 1) n x hcur']
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- Once the current epoch is past the challenge epoch, a simulator state with
a known scalar is definitionally the honest DDH-CKA epoch runner. -/
lemma ddhMultiEpochSimRun_after_challenge_some_eq_runEpochs
    (g aG bG cG prevPub : G) (tStar currentEpoch remaining : ℕ) (prevSecret : F)
    (hcur : tStar < currentEpoch) :
    ddhMultiEpochSimRun (F := F) g aG bG cG tStar currentEpoch remaining
      (some prevSecret) prevPub =
      runEpochs (ddhCKA (F := F) g) currentEpoch remaining prevPub prevSecret := by
  induction remaining generalizing currentEpoch prevSecret prevPub with
  | zero =>
      simp [ddhMultiEpochSimRun, runEpochs]
  | succ n ih =>
      have hpre : currentEpoch + 1 ≠ tStar := by omega
      have hchal : currentEpoch ≠ tStar := by omega
      simp [ddhMultiEpochSimRun, runEpochs, ddhCKA, hpre, hchal]
      apply bind_congr
      intro x
      have hcur' : tStar < currentEpoch + 1 := by omega
      rw [ih (x • g) (currentEpoch + 1) x hcur']
      rfl

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- Past the challenge epoch, one fresh honest epoch restores a known scalar
from a simulator state that temporarily does not know the previous secret. -/
lemma ddhMultiEpochSimRun_after_challenge_none_succ_eq_runEpochs
    (g aG bG cG prevPub : G) (tStar currentEpoch n : ℕ) (prevSecret : F)
    (hcur : tStar < currentEpoch) :
    ddhMultiEpochSimRun (F := F) g aG bG cG tStar currentEpoch (n + 1) none prevPub =
      runEpochs (ddhCKA (F := F) g) currentEpoch (n + 1) prevPub prevSecret := by
  have hpre : currentEpoch + 1 ≠ tStar := by omega
  have hchal : currentEpoch ≠ tStar := by omega
  simp [ddhMultiEpochSimRun, runEpochs, ddhCKA, hpre, hchal]
  apply bind_congr
  intro x
  have hcur' : tStar < currentEpoch + 1 := by omega
  rw [ddhMultiEpochSimRun_after_challenge_some_eq_runEpochs
    (F := F) g aG bG cG (x • g) tStar (currentEpoch + 1) n x hcur']
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- Past the challenge epoch, a simulator state with no known scalar is
observationally identical to an honest run for transcript and corruption
reveals. For zero remaining epochs the final receiver scalar may differ, but
the adversary in this game cannot observe it. -/
lemma ddhMultiEpochSimRun_after_challenge_none_visible_eq_runEpochs
    (g aG bG cG prevPub : G) (tStar currentEpoch remaining : ℕ) (prevSecret : F)
    (prefixTranscript : List (G × G)) (prefixStates : List (G ⊕ F))
    (corruptionRequests : List ℕ)
    (guess : List (G × G) → List (G ⊕ F) → ProbComp Bool)
    (hcur : tStar < currentEpoch) :
    evalDist (do
      let result ← ddhMultiEpochSimRun (F := F) g aG bG cG tStar currentEpoch remaining none prevPub
      guess (prefixTranscript ++ result.transcript)
        (computeRevealedStates (prefixStates ++ result.senderStatesAfter)
          corruptionRequests tStar 1)) =
    evalDist (do
      let result ← runEpochs (ddhCKA (F := F) g) currentEpoch remaining prevPub prevSecret
      guess (prefixTranscript ++ result.transcript)
        (computeRevealedStates (prefixStates ++ result.senderStatesAfter)
          corruptionRequests tStar 1)) := by
  cases remaining with
  | zero =>
      simp [ddhMultiEpochSimRun, runEpochs]
  | succ n =>
      simp [ddhMultiEpochSimRun_after_challenge_none_succ_eq_runEpochs
        (F := F) g aG bG cG prevPub tStar currentEpoch n prevSecret hcur]

omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G] in
/-- Real-branch simulator correspondence when `aG` is embedded in the initial
state (`tStar = 1`). The honest run samples the challenge send coins as its
first epoch coins; the DDH simulation samples the same scalar as `b`. -/
lemma multiEpochReal_tStar_one_run_eq_ddhSim (g : G)
    (A : MultiEpochCKAAdversary G G G F)
    (_hA : A.tStar = 1) (a : F) :
    evalDist (do
      let result ← runEpochs (ddhCKA (F := F) g) 1 A.numEpochs (a • g) a
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) =
    evalDist (do
      let b ← $ᵗ F
      let result ← ddhMultiEpochSimRun (F := F) g (a • g) (b • g) ((a * b) • g)
        A.tStar 1 A.numEpochs none (a • g)
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) := by
  cases A with
  | mk tStar numEpochs tStar_le tStar_pos corruptionRequests guess =>
      simp at _hA
      subst tStar
      cases numEpochs with
      | zero => omega
      | succ n =>
          apply evalDist_ext
          intro z
          simp [runEpochs, ddhMultiEpochSimRun, ddhCKA, smul_smul, mul_comm]
          refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
          intro b
          cases n with
          | zero =>
              simp [runEpochs, ddhMultiEpochSimRun, computeRevealedStates, indexFrom,
                filterCorruptionReveals,
                corruptionPermitted, allowCorr, epochFinished]
          | succ n =>
              simp [ddhMultiEpochSimRun_tStar_one_none_succ_eq_runEpochs
                  (F := F) g (a • g) (b • g) ((a * b) • g) (b • g) 2 n b
                  (by omega),
                ddhCKA, computeRevealedStates, indexFrom, filterCorruptionReveals,
                corruptionPermitted, allowCorr, epochFinished]

omit [Fintype F] [DecidableEq F] [SampleableType G] in
/-- Real-branch prefix simulation before the challenge window.

The honest runner samples ordinary epoch coins until the epoch immediately
before `tStar`. The DDH simulator behaves identically on those epochs while
reserving the DDH samples `a` and `b` for epochs `tStar - 1` and `tStar`. -/
lemma multiEpochReal_prefix_run_eq_ddhSim
    (g : G) (tStar currentEpoch remaining : ℕ)
    (prevSecret : F) (prevPub : G)
    (prefixTranscript : List (G × G))
    (prefixStates : List (G ⊕ F))
    (corruptionRequests : List ℕ)
    (guess : List (G × G) → List (G ⊕ F) → ProbComp Bool)
    (hbefore : currentEpoch < tStar)
    (hwithin : tStar < currentEpoch + remaining)
    (hprefixStatesLen : prefixStates.length + 1 = currentEpoch)
    (hprev : prevPub = prevSecret • g) :
    evalDist (do
      let result ← runEpochs (ddhCKA (F := F) g) currentEpoch remaining prevPub prevSecret
      guess (prefixTranscript ++ result.transcript)
        (computeRevealedStates (prefixStates ++ result.senderStatesAfter)
          corruptionRequests tStar 1)) =
    evalDist (do
      let a ← $ᵗ F
      let b ← $ᵗ F
      let result ← ddhMultiEpochSimRun (F := F) g (a • g) (b • g) ((a * b) • g)
        tStar currentEpoch remaining (some prevSecret) prevPub
      guess (prefixTranscript ++ result.transcript)
        (computeRevealedStates (prefixStates ++ result.senderStatesAfter)
          corruptionRequests tStar 1)) := by
  induction remaining generalizing currentEpoch prevSecret prevPub prefixTranscript prefixStates with
  | zero => omega
  | succ n ih =>
      subst prevPub
      apply evalDist_ext
      intro z
      by_cases hpre : currentEpoch + 1 = tStar
      · cases n with
        | zero => omega
        | succ n =>
            simp [runEpochs, ddhMultiEpochSimRun, ddhCKA, hpre, smul_smul, mul_comm]
            refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
            intro a
            refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
            intro b
            let nextTranscript : List (G × G) :=
              prefixTranscript ++ [(a • g, (prevSecret * a) • g), (b • g, (a * b) • g)]
            let realStates : List (G ⊕ F) :=
              prefixStates ++ [Sum.inr a, Sum.inr b]
            let simStates : List (G ⊕ F) :=
              prefixStates ++ [Sum.inr default, Sum.inr default]
            have hreal_to_sim :
                Pr[= z | do
                  let result ← runEpochs (ddhCKA (F := F) g) (tStar + 1) n (b • g) b
                  guess (nextTranscript ++ result.transcript)
                    (computeRevealedStates (realStates ++ result.senderStatesAfter)
                      corruptionRequests tStar 1)] =
                Pr[= z | do
                  let result ← runEpochs (ddhCKA (F := F) g) (tStar + 1) n (b • g) b
                  guess (nextTranscript ++ result.transcript)
                    (computeRevealedStates (simStates ++ result.senderStatesAfter)
                      corruptionRequests tStar 1)] := by
              refine probOutput_bind_congr'
                (runEpochs (ddhCKA (F := F) g) (tStar + 1) n (b • g) b) z ?_
              intro result
              have hforbidPre : ¬ corruptionPermitted (prefixStates.length + 1) tStar 1 := by
                rw [hprefixStatesLen]
                unfold corruptionPermitted allowCorr epochFinished
                omega
              have hhidePre := computeRevealedStates_replace_forbidden
                (statePrefix := prefixStates)
                (x := Sum.inr a) (y := (Sum.inr default : G ⊕ F))
                (suffix := Sum.inr b :: result.senderStatesAfter)
                corruptionRequests tStar 1 hforbidPre
              have hforbidStar :
                  ¬ corruptionPermitted
                    ((prefixStates ++ [Sum.inr (α := G) (β := F) default]).length + 1)
                    tStar 1 := by
                simp [hprefixStatesLen]
                unfold corruptionPermitted allowCorr epochFinished
                omega
              have hhideStar := computeRevealedStates_replace_forbidden
                (statePrefix := prefixStates ++ [Sum.inr (α := G) (β := F) default])
                (x := Sum.inr b) (y := (Sum.inr default : G ⊕ F))
                (suffix := result.senderStatesAfter)
                corruptionRequests tStar 1 hforbidStar
              have hreveal :
                  computeRevealedStates (realStates ++ result.senderStatesAfter)
                      corruptionRequests tStar 1 =
                    computeRevealedStates (simStates ++ result.senderStatesAfter)
                      corruptionRequests tStar 1 := by
                calc
                  computeRevealedStates (realStates ++ result.senderStatesAfter)
                      corruptionRequests tStar 1 =
                    computeRevealedStates
                      ((prefixStates ++ [Sum.inr (α := G) (β := F) default, Sum.inr b]) ++
                        result.senderStatesAfter) corruptionRequests tStar 1 := by
                      simpa [realStates, List.append_assoc] using hhidePre
                  _ =
                    computeRevealedStates (simStates ++ result.senderStatesAfter)
                      corruptionRequests tStar 1 := by
                      simpa [simStates, List.append_assoc] using hhideStar
              simp [hreveal]
            have htail := ddhMultiEpochSimRun_after_challenge_none_visible_eq_runEpochs
              (F := F) g (a • g) (b • g) ((a * b) • g) (b • g)
              tStar (tStar + 1) n b nextTranscript simStates corruptionRequests guess
              (by omega)
            simpa [nextTranscript, realStates, simStates, List.append_assoc] using
              hreal_to_sim.trans (evalDist_ext_iff.mp htail z).symm
      · have hchal : currentEpoch ≠ tStar := by omega
        simp [runEpochs, ddhMultiEpochSimRun, ddhCKA, hpre, hchal, smul_smul, mul_comm]
        rw [probOutput_bind_bind_bind_rotate]
        refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
        intro x
        have hbefore' : currentEpoch + 1 < tStar := by omega
        have hwithin' : tStar < currentEpoch + 1 + n := by omega
        have hprefixStatesLen' :
            (prefixStates ++ [Sum.inr x]).length + 1 = currentEpoch + 1 := by
          simp [hprefixStatesLen]
        have hih := ih (currentEpoch + 1) x (x • g)
          (prefixTranscript ++ [(x • g, (prevSecret * x) • g)])
          (prefixStates ++ [Sum.inr x])
          hbefore' hwithin' hprefixStatesLen' rfl
        simpa [List.append_assoc] using (evalDist_ext_iff.mp hih z)

omit [Fintype F] [DecidableEq F] [SampleableType G] in
/-- Real-branch simulator correspondence when `aG` is embedded at epoch
`tStar - 1` after an honest initialization. -/
lemma multiEpochReal_tStar_ne_one_run_eq_ddhSim (g : G)
    (A : MultiEpochCKAAdversary G G G F)
    (_hA : A.tStar ≠ 1) (k : F) :
    evalDist (do
      let result ← runEpochs (ddhCKA (F := F) g) 1 A.numEpochs (k • g) k
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) =
    evalDist (do
      let a ← $ᵗ F
      let b ← $ᵗ F
      let result ← ddhMultiEpochSimRun (F := F) g (a • g) (b • g) ((a * b) • g)
        A.tStar 1 A.numEpochs (some k) (k • g)
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) := by
  have hbefore : 1 < A.tStar := by
    have hpos : 0 < A.tStar := A.tStar_pos
    omega
  have hwithin : A.tStar < 1 + A.numEpochs := by
    have hle : A.tStar ≤ A.numEpochs := A.tStar_le
    omega
  exact multiEpochReal_prefix_run_eq_ddhSim g A.tStar 1 A.numEpochs k (k • g)
    [] [] A.corruptionRequests A.guess hbefore hwithin rfl rfl

omit [Fintype F] [DecidableEq F] [SampleableType G] in
/-- Real-branch correctness of the restricted multi-epoch DDH simulator. -/
lemma multiEpochRealExp_eq_ddhExpReal (g : G)
    (A : MultiEpochCKAAdversary G G G F) :
    evalDist (multiEpochCKARealExp (ddhCKA (F := F) g) 1 A) =
      evalDist (ddhExpReal (F := F) g (multiEpochAdvToDDHAdv A)) := by
  apply evalDist_ext
  intro z
  by_cases hA : A.tStar = 1
  · simp [multiEpochCKARealExp, ddhExpReal, multiEpochAdvToDDHAdv, ddhCKA, hA]
    refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
    intro a
    simpa [hA, ddhCKA] using
      (evalDist_ext_iff.mp (multiEpochReal_tStar_one_run_eq_ddhSim g A hA a)) z
  · simp [multiEpochCKARealExp, ddhExpReal, multiEpochAdvToDDHAdv, ddhCKA, hA]
    rw [probOutput_bind_bind_bind_rotate]
    refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
    intro k
    exact (evalDist_ext_iff.mp (multiEpochReal_tStar_ne_one_run_eq_ddhSim g A hA k)) z

omit [DecidableEq F] [DecidableEq G] in
/-- Random-branch simulator correspondence when `aG` is embedded in the
initial state (`tStar = 1`). The random challenge output sampled in `G` is
matched to the DDH random scalar via the generator bijection. -/
lemma multiEpochRand_tStar_one_run_eq_ddhSim (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (A : MultiEpochCKAAdversary G G G F)
    (_hA : A.tStar = 1) (a : F) :
    evalDist (do
      let result ← runEpochsRand (ddhCKA (F := F) g) A.tStar 1 A.numEpochs (a • g) a
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) =
    evalDist (do
      let b ← $ᵗ F
      let c ← $ᵗ F
      let result ← ddhMultiEpochSimRun (F := F) g (a • g) (b • g) (c • g)
        A.tStar 1 A.numEpochs none (a • g)
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) := by
  cases A with
  | mk tStar numEpochs tStar_le tStar_pos corruptionRequests guess =>
      simp at _hA
      subst tStar
      cases numEpochs with
      | zero => omega
      | succ n =>
          apply evalDist_ext
          intro z
          simp [runEpochsRand, ddhMultiEpochSimRun, ddhCKA, smul_smul, mul_comm]
          refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
          intro b
          trans Pr[= z | do
            let c ← $ᵗ F
            let result ← runEpochsRand (ddhCKA (F := F) g) 1 2 n (b • g) b
            guess ((b • g, c • g) :: result.transcript)
              (computeRevealedStates (Sum.inr b :: result.senderStatesAfter)
                corruptionRequests 1 1)]
          · symm
            exact probOutput_bind_bijective_uniform_cross
              (α := F) (β := G) (fun c : F => c • g) hg
              (fun randOutput : G => do
                let result ← runEpochsRand (ddhCKA (F := F) g) 1 2 n (b • g) b
                guess ((b • g, randOutput) :: result.transcript)
                  (computeRevealedStates (Sum.inr b :: result.senderStatesAfter)
                    corruptionRequests 1 1)) z
          · refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
            intro c
            have htailRand := runEpochsRand_after_challenge_eq_runEpochs
              (F := F) g 1 2 n (b • g) b (by omega)
            have htailSim := ddhMultiEpochSimRun_after_challenge_none_visible_eq_runEpochs
              (F := F) g (a • g) (b • g) (c • g) (b • g)
              1 2 n b [(b • g, c • g)] [Sum.inr (α := G) (β := F) default]
              corruptionRequests guess (by omega)
            trans Pr[= z | do
              let result ← runEpochs (ddhCKA (F := F) g) 2 n (b • g) b
              guess ((b • g, c • g) :: result.transcript)
                (computeRevealedStates (Sum.inr b :: result.senderStatesAfter)
                  corruptionRequests 1 1)]
            · simp [htailRand]
            · trans Pr[= z | do
                let result ← runEpochs (ddhCKA (F := F) g) 2 n (b • g) b
                guess ((b • g, c • g) :: result.transcript)
                  (computeRevealedStates (Sum.inr default :: result.senderStatesAfter)
                    corruptionRequests 1 1)]
              · refine probOutput_bind_congr'
                  (runEpochs (ddhCKA (F := F) g) 2 n (b • g) b) z ?_
                intro result
                have hhide := computeRevealedStates_replace_forbidden
                  (statePrefix := ([] : List (G ⊕ F)))
                  (x := Sum.inr b) (y := (Sum.inr default : G ⊕ F))
                  (suffix := result.senderStatesAfter)
                  corruptionRequests 1 1 (not_corruptionPermitted_tStar_delta_one 1)
                have hhide' :
                    computeRevealedStates (Sum.inr b :: result.senderStatesAfter)
                        corruptionRequests 1 1 =
                      computeRevealedStates (Sum.inr default :: result.senderStatesAfter)
                        corruptionRequests 1 1 := by
                  simpa using hhide
                rw [hhide']
              · simpa using (evalDist_ext_iff.mp htailSim z).symm

omit [DecidableEq F] [DecidableEq G] in
/-- Random-branch prefix simulation before the challenge window.

This is the random-output analogue of
`multiEpochReal_prefix_run_eq_ddhSim`: at the challenge epoch the CKA game
samples a uniform `G`, while DDH samples a scalar and maps it through
`c ↦ c • g`. -/
lemma multiEpochRand_prefix_run_eq_ddhSim
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (tStar currentEpoch remaining : ℕ)
    (prevSecret : F) (prevPub : G)
    (prefixTranscript : List (G × G))
    (prefixStates : List (G ⊕ F))
    (corruptionRequests : List ℕ)
    (guess : List (G × G) → List (G ⊕ F) → ProbComp Bool)
    (hbefore : currentEpoch < tStar)
    (hwithin : tStar < currentEpoch + remaining)
    (hprefixStatesLen : prefixStates.length + 1 = currentEpoch)
    (hprev : prevPub = prevSecret • g) :
    evalDist (do
      let result ← runEpochsRand (ddhCKA (F := F) g) tStar currentEpoch remaining prevPub prevSecret
      guess (prefixTranscript ++ result.transcript)
        (computeRevealedStates (prefixStates ++ result.senderStatesAfter)
          corruptionRequests tStar 1)) =
    evalDist (do
      let a ← $ᵗ F
      let b ← $ᵗ F
      let c ← $ᵗ F
      let result ← ddhMultiEpochSimRun (F := F) g (a • g) (b • g) (c • g)
        tStar currentEpoch remaining (some prevSecret) prevPub
      guess (prefixTranscript ++ result.transcript)
        (computeRevealedStates (prefixStates ++ result.senderStatesAfter)
          corruptionRequests tStar 1)) := by
  induction remaining generalizing currentEpoch prevSecret prevPub prefixTranscript prefixStates with
  | zero => omega
  | succ n ih =>
      subst prevPub
      apply evalDist_ext
      intro z
      by_cases hpre : currentEpoch + 1 = tStar
      · cases n with
        | zero => omega
        | succ n =>
            have hchal : currentEpoch ≠ tStar := by omega
            simp [runEpochsRand, ddhMultiEpochSimRun, ddhCKA, hpre, hchal, smul_smul,
              mul_comm]
            refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
            intro a
            refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
            intro b
            trans Pr[= z | do
              let c ← $ᵗ F
              let result ← runEpochsRand (ddhCKA (F := F) g) tStar (tStar + 1) n (b • g) b
              guess (prefixTranscript ++ (a • g, (prevSecret * a) • g) ::
                  (b • g, c • g) :: result.transcript)
                (computeRevealedStates
                  (prefixStates ++ Sum.inr a :: Sum.inr b :: result.senderStatesAfter)
                  corruptionRequests tStar 1)]
            · symm
              exact probOutput_bind_bijective_uniform_cross
                (α := F) (β := G) (fun c : F => c • g) hg
                (fun randOutput : G => do
                  let result ← runEpochsRand (ddhCKA (F := F) g) tStar (tStar + 1) n
                    (b • g) b
                  guess (prefixTranscript ++ (a • g, (prevSecret * a) • g) ::
                      (b • g, randOutput) :: result.transcript)
                    (computeRevealedStates
                      (prefixStates ++ Sum.inr a :: Sum.inr b :: result.senderStatesAfter)
                      corruptionRequests tStar 1)) z
            · refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
              intro c
              let nextTranscript : List (G × G) :=
                prefixTranscript ++ [(a • g, (prevSecret * a) • g), (b • g, c • g)]
              let realStates : List (G ⊕ F) :=
                prefixStates ++ [Sum.inr a, Sum.inr b]
              let simStates : List (G ⊕ F) :=
                prefixStates ++ [Sum.inr default, Sum.inr default]
              have htailRand := runEpochsRand_after_challenge_eq_runEpochs
                (F := F) g tStar (tStar + 1) n (b • g) b (by omega)
              have htailSim := ddhMultiEpochSimRun_after_challenge_none_visible_eq_runEpochs
                (F := F) g (a • g) (b • g) (c • g) (b • g)
                tStar (tStar + 1) n b nextTranscript simStates corruptionRequests guess
                (by omega)
              trans Pr[= z | do
                let result ← runEpochs (ddhCKA (F := F) g) (tStar + 1) n (b • g) b
                guess (nextTranscript ++ result.transcript)
                  (computeRevealedStates (realStates ++ result.senderStatesAfter)
                    corruptionRequests tStar 1)]
              · simp [nextTranscript, realStates, htailRand, List.append_assoc]
              · trans Pr[= z | do
                  let result ← runEpochs (ddhCKA (F := F) g) (tStar + 1) n (b • g) b
                  guess (nextTranscript ++ result.transcript)
                    (computeRevealedStates (simStates ++ result.senderStatesAfter)
                      corruptionRequests tStar 1)]
                · refine probOutput_bind_congr'
                    (runEpochs (ddhCKA (F := F) g) (tStar + 1) n (b • g) b) z ?_
                  intro result
                  have hforbidPre : ¬ corruptionPermitted (prefixStates.length + 1) tStar 1 := by
                    rw [hprefixStatesLen]
                    unfold corruptionPermitted allowCorr epochFinished
                    omega
                  have hhidePre := computeRevealedStates_replace_forbidden
                    (statePrefix := prefixStates)
                    (x := Sum.inr a) (y := (Sum.inr default : G ⊕ F))
                    (suffix := Sum.inr b :: result.senderStatesAfter)
                    corruptionRequests tStar 1 hforbidPre
                  have hforbidStar :
                      ¬ corruptionPermitted
                        ((prefixStates ++ [Sum.inr (α := G) (β := F) default]).length + 1)
                        tStar 1 := by
                    simp [hprefixStatesLen]
                    unfold corruptionPermitted allowCorr epochFinished
                    omega
                  have hhideStar := computeRevealedStates_replace_forbidden
                    (statePrefix := prefixStates ++ [Sum.inr (α := G) (β := F) default])
                    (x := Sum.inr b) (y := (Sum.inr default : G ⊕ F))
                    (suffix := result.senderStatesAfter)
                    corruptionRequests tStar 1 hforbidStar
                  have hreveal :
                      computeRevealedStates (realStates ++ result.senderStatesAfter)
                          corruptionRequests tStar 1 =
                        computeRevealedStates (simStates ++ result.senderStatesAfter)
                          corruptionRequests tStar 1 := by
                    calc
                      computeRevealedStates (realStates ++ result.senderStatesAfter)
                          corruptionRequests tStar 1 =
                        computeRevealedStates
                          ((prefixStates ++ [Sum.inr (α := G) (β := F) default, Sum.inr b]) ++
                            result.senderStatesAfter) corruptionRequests tStar 1 := by
                          simpa [realStates, List.append_assoc] using hhidePre
                      _ =
                        computeRevealedStates (simStates ++ result.senderStatesAfter)
                          corruptionRequests tStar 1 := by
                          simpa [simStates, List.append_assoc] using hhideStar
                  simp [hreveal]
                · simpa [nextTranscript, simStates, List.append_assoc] using
                    (evalDist_ext_iff.mp htailSim z).symm
      · have hchal : currentEpoch ≠ tStar := by omega
        simp [runEpochsRand, ddhMultiEpochSimRun, ddhCKA, hpre, hchal, smul_smul, mul_comm]
        rw [probOutput_bind_bind_bind_bind_rotate]
        refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
        intro x
        have hbefore' : currentEpoch + 1 < tStar := by omega
        have hwithin' : tStar < currentEpoch + 1 + n := by omega
        have hprefixStatesLen' :
            (prefixStates ++ [Sum.inr x]).length + 1 = currentEpoch + 1 := by
          simp [hprefixStatesLen]
        have hih := ih (currentEpoch + 1) x (x • g)
          (prefixTranscript ++ [(x • g, (prevSecret * x) • g)])
          (prefixStates ++ [Sum.inr x])
          hbefore' hwithin' hprefixStatesLen' rfl
        simpa [List.append_assoc] using (evalDist_ext_iff.mp hih z)

omit [DecidableEq F] [DecidableEq G] in
/-- Random-branch simulator correspondence when `aG` is embedded at epoch
`tStar - 1` after an honest initialization. -/
lemma multiEpochRand_tStar_ne_one_run_eq_ddhSim (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (A : MultiEpochCKAAdversary G G G F)
    (_hA : A.tStar ≠ 1) (k : F) :
    evalDist (do
      let result ← runEpochsRand (ddhCKA (F := F) g) A.tStar 1 A.numEpochs (k • g) k
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) =
    evalDist (do
      let a ← $ᵗ F
      let b ← $ᵗ F
      let c ← $ᵗ F
      let result ← ddhMultiEpochSimRun (F := F) g (a • g) (b • g) (c • g)
        A.tStar 1 A.numEpochs (some k) (k • g)
      A.guess result.transcript
        (computeRevealedStates result.senderStatesAfter A.corruptionRequests A.tStar 1)) := by
  have hbefore : 1 < A.tStar := by
    have hpos : 0 < A.tStar := A.tStar_pos
    omega
  have hwithin : A.tStar < 1 + A.numEpochs := by
    have hle : A.tStar ≤ A.numEpochs := A.tStar_le
    omega
  exact multiEpochRand_prefix_run_eq_ddhSim g hg A.tStar 1 A.numEpochs k (k • g)
    [] [] A.corruptionRequests A.guess hbefore hwithin rfl rfl

omit [DecidableEq F] [DecidableEq G] in
/-- Random-branch correctness of the restricted multi-epoch DDH simulator.

The bijection hypothesis is needed only in this branch, where the restricted
CKA game samples the challenge output from `G` while DDH samples a scalar and
maps it through `c ↦ c • g`. -/
lemma multiEpochRandExp_eq_ddhExpRand (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (A : MultiEpochCKAAdversary G G G F) :
    evalDist (multiEpochCKARandExp (ddhCKA (F := F) g) 1 A) =
      evalDist (ddhExpRand (F := F) g (multiEpochAdvToDDHAdv A)) := by
  apply evalDist_ext
  intro z
  by_cases hA : A.tStar = 1
  · simp [multiEpochCKARandExp, ddhExpRand, multiEpochAdvToDDHAdv, ddhCKA, hA]
    refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
    intro a
    simpa [hA, ddhCKA] using
      (evalDist_ext_iff.mp (multiEpochRand_tStar_one_run_eq_ddhSim g hg A hA a)) z
  · simp [multiEpochCKARandExp, ddhExpRand, multiEpochAdvToDDHAdv, ddhCKA, hA]
    rw [probOutput_bind_bind_bind_bind_rotate]
    refine probOutput_bind_congr' ($ᵗ F : ProbComp F) z ?_
    intro k
    exact (evalDist_ext_iff.mp (multiEpochRand_tStar_ne_one_run_eq_ddhSim g hg A hA k)) z

omit [DecidableEq F] in
/-- Pointwise reduction bound for the restricted multi-epoch game.

This is the remaining proof obligation for the auxiliary `CKASecureDelta`
entry point: the simulator in `multiEpochAdvToDDHAdv` must match the real
multi-epoch game in the real DDH branch and the random multi-epoch game in the
random DDH branch. -/
lemma multiEpochAdvantage_le_ddhAdvantage (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (A : MultiEpochCKAAdversary G G G F) :
    multiEpochAdvantage (ddhCKA (F := F) g) 1 A ≤
      ddhDistAdvantage (F := F) g (multiEpochAdvToDDHAdv A) := by
  unfold multiEpochAdvantage ddhDistAdvantage
  have hreal :
      Pr[= true | multiEpochCKARealExp (ddhCKA (F := F) g) 1 A] =
        Pr[= true | ddhExpReal (F := F) g (multiEpochAdvToDDHAdv A)] :=
    probOutput_congr rfl (multiEpochRealExp_eq_ddhExpReal g A)
  have hrand :
      Pr[= true | multiEpochCKARandExp (ddhCKA (F := F) g) 1 A] =
        Pr[= true | ddhExpRand (F := F) g (multiEpochAdvToDDHAdv A)] :=
    probOutput_congr rfl (multiEpochRandExp_eq_ddhExpRand g hg A)
  rw [hreal, hrand]

omit [DecidableEq F] in
/-- **Theorem 3** (restricted multi-epoch game, auxiliary, Δ=1):

If every DDH adversary has advantage ≤ ε, then the DDH-CKA scheme is
`CKASecureDelta` with Δ=1 in the restricted non-adaptive multi-epoch game.

**Note**: This targets `CKASecureDelta` from `MultiEpochGame.lean` — a
restricted non-adaptive game where the adversary commits upfront. This is
NOT the paper's full Figure 3 model. For the paper-faithful adaptive
statement, see `ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_cka_security_delta (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    CKASecureDelta (ddhCKA (F := F) g) 1 ε := by
  exact CKASecureDelta_of_reduction g ε multiEpochAdvToDDHAdv
    (multiEpochAdvantage_le_ddhAdvantage g hg) hDDH

/-- **Theorem 3** (Figure 3 formulation with adaptive oracles):

Helper two-game bound for the concrete Figure 3 reduction. This is the
real-vs-random presentation used internally for reductions; the paper-facing
hidden-bit consequence is `figure3GuessAdvantage_le_ddhAdvantage`. -/
theorem figure3Advantage_le_ddhAdvantage (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ)
    (A : Figure3.Figure3Adversary F G G G F) :
    Figure3.figure3Advantage (ddhCKAWithCoins (F := F) g) tStar 1 A ≤
      ddhDistAdvantage (F := F) g (figure3AdvToDDHAdv (tStar, A)) := by
  unfold Figure3.figure3Advantage ddhDistAdvantage ProbComp.boolDistAdvantage
  have hreal :
      Pr[= true | Figure3.figure3Exp (ddhCKAWithCoins (F := F) g) tStar 1 false A] =
        Pr[= true | ddhExpReal (F := F) g (figure3AdvToDDHAdv (tStar, A))] :=
    probOutput_congr rfl (figure3Exp_real_eq_ddhExpReal g hg tStar A)
  have hrand :
      Pr[= true | Figure3.figure3Exp (ddhCKAWithCoins (F := F) g) tStar 1 true A] =
        Pr[= true | ddhExpRand (F := F) g (figure3AdvToDDHAdv (tStar, A))] :=
    probOutput_congr rfl (figure3Exp_rand_eq_ddhExpRand g hg tStar A)
  rw [hreal, hrand]

/-- Paper-facing hidden-bit bound for the concrete Figure 3 reduction. -/
theorem figure3GuessAdvantage_le_ddhAdvantage (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (tStar : ℕ)
    (A : Figure3.Figure3Adversary F G G G F) :
    Figure3.figure3GuessAdvantage (ddhCKAWithCoins (F := F) g) tStar 1 A ≤
      ddhDistAdvantage (F := F) g (figure3AdvToDDHAdv (tStar, A)) := by
  simpa [Figure3.figure3GuessAdvantage_eq_figure3Advantage] using
    figure3Advantage_le_ddhAdvantage g hg tStar A

/-- Auxiliary Figure 3 wrapper in the derived two-game presentation.

This keeps the real-vs-random surface available for reduction-oriented proofs;
the primary paper-facing theorem is `ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_figure3_cka_security_two_game (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    Figure3.Figure3CKASecure (ddhCKAWithCoins (F := F) g) 1 ε := by
  intro tStar A
  exact le_trans (figure3Advantage_le_ddhAdvantage g hg tStar A) (hDDH _)

/-- **Theorem 3** (Figure 3 formulation with adaptive oracles):

If G is (t,ε)-DDH-secure, then the DDH-based CKA scheme is (t, Δ=1, ε)-secure
in the full Figure 3 game with adaptive oracle interaction, party-specific
corruption, and bad-randomness oracles.

This is the paper-faithful hidden-bit statement over the upgraded game model.
The concrete reduction is captured by `figure3GuessAdvantage_le_ddhAdvantage`,
and the theorem packages that pointwise bound into the Definition 13 surface. -/
theorem ddh_implies_figure3_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    Figure3.Figure3CKASecurePaper (ddhCKAWithCoins (F := F) g) 1 ε := by
  intro tStar A
  exact le_trans (figure3GuessAdvantage_le_ddhAdvantage g hg tStar A) (hDDH _)

end CKA

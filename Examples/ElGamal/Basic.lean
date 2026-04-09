/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import Examples.ElGamal.Common
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# ElGamal Encryption: IND-CPA via the generic one-time lift

This file defines ElGamal encryption over a module `Module F G` and treats the security proof as
a one-time DDH client of the generic IND-CPA lift in `AsymmEncAlg`.

## Mathematical notation

We use additive / EC-style notation throughout:

| Textbook (multiplicative) | This file (additive)             |
|---------------------------|----------------------------------|
| `g^a`                     | `a • gen`                        |
| `g^a · g^b = g^{a+b}`     | `a • gen + b • gen`              |
| `(g^a)^b = g^{ab}`        | `b • (a • gen) = (b * a) • gen` |
| `m · g^{ab}`              | `m + (a * b) • gen`              |

Here `F` is the scalar field (for example `ZMod p`), `G` is the additive group of ciphertext
payloads (for example elliptic-curve points), and `gen : G` is a fixed public generator.

## Proof structure

**Security games**

**IND-CPA₁ instantiated for ElGamal** (`AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp`):
  sample `b ← {0,1}` and `(pk, sk) ← KeyGen`;
  adversary chooses `(m₀, m₁)`; compute `c := (c₁, c₂) ← Encrypt(pk, m_b)`;
  adversary receives `(c₁, c₂)` and outputs `b'`; wins if `b' = b`.
**DDH** (`DiffieHellman.ddhExp`):
  sample `a, b ← F` and a bit `β`; let `A = a•g`, `B = b•g`;
  set `T = (a·b)•g` if `β = 1`, else `T = c•g` with `c ← F`;
  adversary receives `(g, A, B, T)` and outputs `β'`; wins if `β' = β`.
  The two branches are also defined separately (adversary outputs a bit; no built-in win check):
  - **DDH_real** (`ddhExpReal`): `a, b ← F`; adversary gets `(g, a•g, b•g, (a·b)•g)`.
  - **DDH_rand** (`ddhExpRand`): `a, b, c ← F`; adversary gets `(g, a•g, b•g, c•g)`.

1. ElGamal definition and correctness.
2. One-time DDH bridge:
   Write `R(adv)` for the DDH adversary (reduction) built from a one-time IND-CPA₁ adversary `adv`.
   Write `D(X)` for `evalDist(X)`, the output distribution (over `Bool`) of game `X`.

   `IND_CPA_OneTime_DDHReduction` - defines `R(adv)`: given challenge DDH tuple `(g, A, B, T)`,
      set `pk = A`, challenge IND-CPA₁ ciphertext `(c₁, c₂) = (B, T + m_b)`, run `adv`,
      and output `b == b'` (IND-CPA guess) as the DDH guess.
   `IND_CPA_OneTime_game_evalDist_eq_ddhExpReal` -
      `D(IND_CPA₁(adv)) = D(DDH_real(R(adv)))`: in the real branch `T = (a·b)•g`, so the
      ciphertext `(B, T + m_b) = (b•g, m_b + (a·b)•g)` is a valid ElGamal encryption of
      `m_b` under `pk = a•g` with randomness `b` — identical to the IND-CPA₁ game.
   `IND_CPA_OneTime_DDHReduction_rand_half` -
      `Pr[DDH_rand(R(adv)) = true] = 1/2` (uniform mask hides the challenge bit).
   `elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage` -
      `|Adv^{IND-CPA₁}(adv)| = 2 · Adv^{DDH}(R(adv))`.
      Combines the two previous results:
      `|Adv^{IND-CPA₁}| = |Pr[IND_CPA₁=true] - 1/2|`  (definition)
                        `= |Pr[DDH_real(R)=true] - 1/2|`  (by `evalDist_eq_ddhExpReal`)
                        `= |Pr[DDH_real(R)=true] - Pr[DDH_rand(R)=true]|`  (by `rand_half`)
                        `= 2 · Adv^{DDH}(R)`  (by `ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage`).
3. Final theorem:
   `elGamal_IND_CPA_le_q_mul_ddh` is a direct instantiation of
   `AsymmEncAlg.IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound`
   with one-time loss `2 * ε`.
-/

open OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- ElGamal encryption over a module `Module F G` with generator `gen : G`.

Key generation samples a scalar `sk ← $ᵗ F` and returns `(sk • gen, sk)`.
Encryption of `msg` under public key `pk` samples `r ← $ᵗ F` and returns
`(r • gen, msg + r • pk)`. Decryption recovers `msg` as `c₂ - sk • c₁`. -/
@[simps!] def elGamalAsymmEnc (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : AsymmEncAlg ProbComp
    (M := G) (PK := G) (SK := F) (C := G × G) where
  keygen := do
    let sk ← $ᵗ F
    return (sk • gen, sk)
  encrypt := fun pk msg => do
    let r ← $ᵗ F
    return (r • gen, msg + r • pk)
  decrypt := fun sk (c₁, c₂) =>
    return (some (c₂ - sk • c₁))

namespace elGamalAsymmEnc

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

/-- ElGamal decryption perfectly inverts encryption: `Dec(sk, Enc(pk, msg)) = msg`. -/
theorem correct [DecidableEq G] :
    (elGamalAsymmEnc F G gen).PerfectlyCorrect ProbCompRuntime.probComp := by
  have hcancel : ∀ (msg : G) (sk r : F),
      msg + r • (sk • gen) - sk • (r • gen) = msg := by
    intro msg sk r
    have : r • (sk • gen) = sk • (r • gen) := by
      rw [← mul_smul, ← mul_smul, mul_comm]
    rw [this, add_sub_cancel_right]
  simp [AsymmEncAlg.PerfectlyCorrect, ProbCompRuntime.probComp, ProbCompRuntime.evalDist,
    AsymmEncAlg.CorrectExp, elGamalAsymmEnc, hcancel,
    HasEvalPMF.toSPMF_eq, SPMF.probFailure_liftM, HasEvalPMF.probFailure_eq_zero]

section IND_CPA

variable [DecidableEq G]

local instance : Inhabited G := ⟨0⟩

/-- One-time DDH reduction for ElGamal. On input `(gen, A, B, T)`, use `A` as the ElGamal public
key, form the challenge ciphertext `(B, T + m_b)`, and return whether the one-time adversary
guessed the hidden bit `b`. -/
def IND_CPA_OneTime_DDHReduction
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    DiffieHellman.DDHAdversary F G := fun _ A B T => do
  let (m₁, m₂, st) ← adv.chooseMessages A
  let bit ← ($ᵗ Bool : ProbComp Bool)
  let c : G × G := (B, T + if bit then m₁ else m₂)
  let bit' ← adv.distinguish st c
  pure (bit == bit')

omit [DecidableEq G] in
/-- Real-branch identification for the one-time ElGamal reduction. After unfolding
`IND_CPA_OneTime_Game_ProbComp`, `elGamalAsymmEnc`, `DiffieHellman.ddhExpReal`, and
`IND_CPA_OneTime_DDHReduction`, both sides normalize to the same sample space.

**`D(IND_CPA₁(adv)) = D(DDH_real(R(adv)))`**.
In the real branch, `T = (a·b)•g`, so the reduction's ciphertext
`(B, T + m_b) = (b•g, m_b + (a·b)•g)` is a valid ElGamal encryption of `m_b`
under `pk = a•g` with randomness `b`. -/
private lemma IND_CPA_OneTime_game_evalDist_eq_ddhExpReal
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    evalDist
      (AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
        (encAlg := elGamalAsymmEnc F G gen) adv) =
    evalDist
      (DiffieHellman.ddhExpReal (F := F) gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)) := by
  -- Unfold all definitions to expose the raw sampling sequences on both sides.
  simp only [AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp,
    DiffieHellman.ddhExpReal, IND_CPA_OneTime_DDHReduction,
    elGamalAsymmEnc]
  -- Goal: D₁ = D₂ (two PMFs). Reduce to pointwise: ∀ z, D₁(z) = D₂(z).
  ext z
  -- Rewrite D₁(z) = D₂(z) as Pr[= z | comp₁] = Pr[= z | comp₂] (probOutput form).
  change Pr[= z | _] = Pr[= z | _]
  -- Normalize: unfold <$> as >>= and simplify map/bind.
  simp only [bind_pure_comp, bind_map_left]
  -- The proof now reorders independent samples on both sides to a common order,
  -- peeling off matching outer binds with `probOutput_bind_congr'` (which says:
  -- if both sides start with the same bind `mx`, fix one sample and prove the rest).
  -- `refine ... (fun x => ?_)` applies the lemma and leaves the continuation as a new goal
  -- with `x` fixed in scope.
  --
  -- LHS sampling order: b; sk; (m₀,m₁,st); r   (IND-CPA game)
  -- RHS sampling order: sk; r; (m₀,m₁,st); b   (DDH real with reduction)
  -- Target order:       sk; (m₀,m₁,st); r; b
  --
  -- Step 1: LHS: swap b past sk → sk; b; (m₀,m₁,st); r
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Both now start with sk ← $ᵗF. Fix sk.
  refine probOutput_bind_congr' ($ᵗ F) z (fun sk => ?_)
  -- Step 2: LHS: swap b past chooseMessages → sk; (m₀,m₁,st); b; r
  rw [probOutput_bind_bind_swap ($ᵗ Bool) (adv.chooseMessages (sk • gen))]
  -- Step 3: RHS: swap r past chooseMessages → sk; (m₀,m₁,st); r; b
  conv_rhs => rw [probOutput_bind_bind_swap ($ᵗ F) (adv.chooseMessages (sk • gen))]
  -- Both now start with chooseMessages. Fix (m₀, m₁, st).
  refine probOutput_bind_congr' (adv.chooseMessages (sk • gen)) z (fun cm => ?_)
  -- Step 4: LHS: swap b past r → sk; (m₀,m₁,st); r; b
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Both now: r ← $ᵗF; b ← $ᵗBool; ... Fix r and b.
  refine probOutput_bind_congr' ($ᵗ F) z (fun r => ?_)
  refine probOutput_bind_congr' ($ᵗ Bool) z (fun bit => ?_)
  -- All samples fixed. Show the ciphertext expressions match:
  -- LHS: (r•gen, m_b + r • (sk • gen))     (ElGamal encryption)
  -- RHS: (r•gen, (sk * r)•gen + m_b)        (DDH real tuple)
  -- These are equal by: r•(sk•gen) = (sk*r)•gen (smul_smul) and commutativity of + and *.
  congr 2
  rw [smul_smul, add_comm, mul_comm]

omit [DecidableEq G] in
/-- Random-branch half lemma for the one-time ElGamal reduction. Under bijectivity of `(· • gen)`,
the DDH-random branch gives a uniform additive mask independent of the challenge bit, so the
adversary can do no better than random guessing.

**`Pr[DDH_rand(R(adv)) = true] = 1/2`**.
Recall `R(adv)` internally samples `b`, builds ciphertext `(B, T + m_b)`, runs `adv`, and
outputs `b == b'`. In the random branch `T = c•g` with independent `c ← F`, so `T + m_b`
is uniform (one-time pad). Thus `adv`'s guess `b'` is independent of `b`, giving
`Pr[b == b'] = 1/2`, i.e. `R(adv)` outputs `true` with probability `1/2`. -/
private lemma IND_CPA_OneTime_DDHReduction_rand_half
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    Pr[= true | DiffieHellman.ddhExpRand (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] = 1 / 2 := by
  -- `inner pk`: DDH_rand(R(adv)) restated with uniform samples over G instead of F.
  -- (Bijectivity of `(· • gen)` justifies this equivalence later in the `calc` block.)
  let inner : G → ProbComp Bool := fun pk => do
    let head ← ($ᵗ G : ProbComp G)
    let mask ← ($ᵗ G : ProbComp G)
    let (m₁, m₂, st) ← adv.chooseMessages pk
    let bit ← ($ᵗ Bool : ProbComp Bool)
    let bit' ← adv.distinguish st (head, mask + if bit then m₁ else m₂)
    pure (decide (bit = bit'))
  -- `f pk bit`: `inner` with `bit` externalized and `mask` moved after `chooseMessages`.
  -- Same distribution, but now we can apply the OTP lemma to show `D(f pk true) = D(f pk false)`.
  let f : G → Bool → ProbComp Bool := fun pk bit => do
    let head ← ($ᵗ G : ProbComp G)
    let (m₁, m₂, st) ← adv.chooseMessages pk
    let mask ← ($ᵗ G : ProbComp G)
    adv.distinguish st (head, mask + if bit then m₁ else m₂)
  -- OTP: uniform `mask` hides the bit, so D(f pk true) = D(f pk false).
  have hf : ∀ pk, evalDist (f pk true) = evalDist (f pk false) := by
    intro pk
    unfold f
    rw [evalDist_bind, evalDist_bind]
    congr 1
    funext head
    rw [evalDist_bind, evalDist_bind]
    congr 1
    funext x
    rcases x with ⟨m₁, m₂, st⟩
    -- Goal: D(mask ← $G; adv.distinguish st (head, mask + m₁))
    --     = D(mask ← $G; adv.distinguish st (head, mask + m₂))
    -- Apply `uniformMaskedCipher_bind_dist_indep` (from Common.lean):
    --   for any h, m₁, m₂, cont: D(y ← U; cont(h, m₁+y)) = D(y ← U; cont(h, m₂+y))
    -- with cont := adv.distinguish st.
    simpa [add_comm] using
      ElGamalExamples.uniformMaskedCipher_bind_dist_indep
        (head := head) (m₁ := m₁) (m₂ := m₂) (cont := adv.distinguish st)
  -- Rewrite `inner pk` as: bit ← $Bool; bit' ← f pk bit; pure (bit == bit').
  -- This just reorders samples in `inner` to isolate `bit` at the outermost level.
  have hrepr : ∀ pk, Pr[= true | inner pk] =
      Pr[= true | do
        let bit ← ($ᵗ Bool : ProbComp Bool)
        let bit' ← f pk bit
        pure (decide (bit = bit'))] := by
    intro pk
    -- Use transitivity through an intermediate reordering:
    --   A (inner):        head; mask; choose; bit; ...
    --   B (intermediate): head; choose; bit; mask; ...  (mask moved after bit)
    --   C (target):       bit; head; choose; mask; ...  (bit moved to front)
    -- A = B by swapping mask past choose and bit.
    -- B = C by swapping bit past head and choose.
    trans Pr[= true | do
      let head ← ($ᵗ G : ProbComp G)
      let x ← adv.chooseMessages pk
      let bit ← ($ᵗ Bool : ProbComp Bool)
      let mask ← ($ᵗ G : ProbComp G)
      let bit' ← adv.distinguish x.2.2 (head, mask + if bit then x.1 else x.2.1)
      pure (decide (bit = bit'))]
    · refine probOutput_bind_congr' ($ᵗ G : ProbComp G) true ?_
      intro head
      -- A → B (under fixed head): swap mask past (choose, bit).
      -- Goal LHS: mask ← $G; choose; bit ← $Bool; ...
      -- Goal RHS: choose; bit ← $Bool; mask ← $G; ...
      -- `probOutput_bind_bind_swap mx my f z` swaps `mx; my` → `my; mx`:
      --   mx = $ᵗG                              (sampling mask)
      --   my = do x ← choose pk; bit ← $Bool; pure (x, bit)  (choose + bit, bundled)
      --   f  = fun mask ⟨x, bit⟩ => ...         (continuation)
      --   z  = true
      simpa [inner, bind_assoc, map_eq_bind_pure_comp] using
        (probOutput_bind_bind_swap
          ($ᵗ G : ProbComp G)
          (do
            let x ← adv.chooseMessages pk
            let bit ← ($ᵗ Bool : ProbComp Bool)
            pure (x, bit))
          (fun mask ⟨x, bit⟩ => do
            let bit' ← adv.distinguish x.2.2 (head, mask + if bit then x.1 else x.2.1)
            pure (decide (bit = bit')))
          true)
    · simpa [f, bind_assoc, map_eq_bind_pure_comp] using
        (probOutput_bind_bind_swap
          (do
            let head ← ($ᵗ G : ProbComp G)
            let x ← adv.chooseMessages pk
            pure (head, x))
          ($ᵗ Bool : ProbComp Bool)
          (fun ⟨head, x⟩ bit => do
            let mask ← ($ᵗ G : ProbComp G)
            let bit' ← adv.distinguish x.2.2 (head, mask + if bit then x.1 else x.2.1)
            pure (decide (bit = bit')))
          true)
  -- Combine hrepr and hf: since inner pk ≡ (bit ← $Bool; bit' ← f pk bit; bit == bit')
  -- and D(f pk true) = D(f pk false), the outcome bit == bit' is uniform, so Pr[true] = 1/2.
  -- `probOutput_decide_eq_uniformBool_half` is the generic lemma for this pattern.
  have hhalf : ∀ pk, Pr[= true | inner pk] = 1 / 2 := by
    intro pk
    rw [hrepr pk]
    exact probOutput_decide_eq_uniformBool_half (f pk) (hf pk)
  -- Final chain: DDH_rand(R(adv)) ≡ pk ← $G; inner pk (by bijectivity of (· • gen)),
  -- and ∀ pk, Pr[inner pk = true] = 1/2 (by hhalf), so the whole thing equals 1/2.
  calc
    Pr[= true | DiffieHellman.ddhExpRand (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] =
        Pr[= true | do
          let pk ← ($ᵗ G : ProbComp G)
          inner pk] := by
      trans Pr[= true | do
        let pk ← ($ᵗ G : ProbComp G)
        let b ← ($ᵗ F : ProbComp F)
        let c ← ($ᵗ F : ProbComp F)
        let (m₁, m₂, st) ← adv.chooseMessages pk
        let bit ← ($ᵗ Bool : ProbComp Bool)
        let bit' ← adv.distinguish st (b • gen, c • gen + if bit then m₁ else m₂)
        pure (decide (bit = bit'))]
      · simpa [DiffieHellman.ddhExpRand, IND_CPA_OneTime_DDHReduction, bind_assoc,
          map_eq_bind_pure_comp,
          show ∀ a b : Bool, (a == b) = decide (a = b) from by decide] using
          (probOutput_bind_bijective_uniform_cross
            (α := F) (β := G) (f := (· • gen)) hg
            (g := fun pk => do
              let b ← ($ᵗ F : ProbComp F)
              let c ← ($ᵗ F : ProbComp F)
              let (m₁, m₂, st) ← adv.chooseMessages pk
              let bit ← ($ᵗ Bool : ProbComp Bool)
              let bit' ← adv.distinguish st (b • gen, c • gen + if bit then m₁ else m₂)
              pure (decide (bit = bit')))
            true)
      · refine probOutput_bind_congr' ($ᵗ G : ProbComp G) true ?_
        intro pk
        trans Pr[= true | do
          let head ← ($ᵗ G : ProbComp G)
          let c ← ($ᵗ F : ProbComp F)
          let (m₁, m₂, st) ← adv.chooseMessages pk
          let bit ← ($ᵗ Bool : ProbComp Bool)
          let bit' ← adv.distinguish st (head, c • gen + if bit then m₁ else m₂)
          pure (decide (bit = bit'))]
        · simpa [bind_assoc, map_eq_bind_pure_comp] using
            (probOutput_bind_bijective_uniform_cross
              (α := F) (β := G) (f := (· • gen)) hg
              (g := fun head => do
                let c ← ($ᵗ F : ProbComp F)
                let (m₁, m₂, st) ← adv.chooseMessages pk
                let bit ← ($ᵗ Bool : ProbComp Bool)
                let bit' ← adv.distinguish st (head, c • gen + if bit then m₁ else m₂)
                pure (decide (bit = bit')))
              true)
        · refine probOutput_bind_congr' ($ᵗ G : ProbComp G) true ?_
          intro head
          simpa [inner, bind_assoc, map_eq_bind_pure_comp] using
            (probOutput_bind_bijective_uniform_cross
              (α := F) (β := G) (f := (· • gen)) hg
              (g := fun mask => do
                let (m₁, m₂, st) ← adv.chooseMessages pk
                let bit ← ($ᵗ Bool : ProbComp Bool)
                let bit' ← adv.distinguish st (head, mask + if bit then m₁ else m₂)
                pure (decide (bit = bit')))
              true)
    _ = Pr[= true | do
          let pk ← ($ᵗ G : ProbComp G)
          ($ᵗ Bool : ProbComp Bool)] :=
      probOutput_bind_congr' ($ᵗ G) true (fun pk => by
        simpa [probOutput_uniformSample] using hhalf pk)
    -- `pk` is unused, so drop it: Pr[= true | pk ← $G; $Bool] = Pr[= true | $Bool] = 1/2.
    _ = 1 / 2 := by
      simp [probOutput_bind_const, probOutput_uniformSample]

omit [DecidableEq G] in
/-- The absolute one-time signed IND-CPA advantage of ElGamal is exactly twice the DDH guess
advantage of the reduction above. The factor `2` is essential because the DDH guess advantage is
defined from the mixed experiment, while the one-time IND-CPA game compares the real and random
branches directly.

**`|Adv^{IND-CPA₁}(adv)| = 2 · Adv^{DDH}(R(adv))`**.
Combines `D(IND_CPA₁(adv)) = D(DDH_real(R(adv)))` and `Pr[DDH_rand(R(adv))=true] = 1/2`
with `ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage` (see proof outline above). -/
theorem elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv| =
      2 * DiffieHellman.ddhGuessAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) := by
  have h_real :
      |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv| =
      |(Pr[= true | DiffieHellman.ddhExpReal (F := F) gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)]).toReal - 1 / 2| := by
    have hprob :
        Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
          (encAlg := elGamalAsymmEnc F G gen) adv] =
        Pr[= true | DiffieHellman.ddhExpReal (F := F) gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] :=
      probOutput_congr rfl (IND_CPA_OneTime_game_evalDist_eq_ddhExpReal adv)
    simpa [AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal] using
      congrArg (fun p : ℝ≥0∞ => |p.toReal - 1 / 2|) hprob
  have h_rand : (1 : ℝ) / 2 =
    (Pr[= true | DiffieHellman.ddhExpRand (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)]).toReal := by
    rw [IND_CPA_OneTime_DDHReduction_rand_half hg adv]
    simp [ENNReal.toReal_ofNat]
  rw [h_real, h_rand]
  exact DiffieHellman.ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage gen
    (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)

/-- **Main theorem.** If an adversary makes at most `q` LR queries and every extracted one-time
ElGamal DDH reduction has guess advantage at most `ε`, then ElGamal has IND-CPA advantage at most
`q * (2 * ε)`. -/
theorem elGamal_IND_CPA_le_q_mul_ddh
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elGamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hddh : ∀ adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen),
      DiffieHellman.ddhGuessAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) ≤ ε) :
    ((elGamalAsymmEnc F G gen).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine AsymmEncAlg.IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound
    (encAlg' := elGamalAsymmEnc F G gen) adversary q (2 * ε) hq ?_
  intro adv
  calc
    |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv|
      = 2 * DiffieHellman.ddhGuessAdvantage gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) :=
            elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
              (F := F) (G := G) (gen := gen) hg adv
    _ ≤ 2 * ε := by
        linarith [hddh adv]

end IND_CPA

end elGamalAsymmEnc

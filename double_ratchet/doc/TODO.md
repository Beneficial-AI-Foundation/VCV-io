# TODO

## Prove the sorry's

There are currently **13 local declarations using `sorry`** across the
formalization:

### Definitional / bridge lemmas — 2 declarations

1. `ddhCKAWithCoins_toCKAScheme` (`DDHCKA.lean`) — derived `CKAScheme` equals
   the original `ddhCKA`; follows by unfolding definitions
2. `CKASecureDelta_implies_CKASecure` (`MultiEpochGame.lean`) — lift a
   single-epoch adversary to a 1-epoch restricted multi-epoch adversary

### Single-epoch DDH-to-CKA warmup — 4 declarations

3. `ckaRealExp_eq_ddhExpReal` (`Theorem3.lean`) — distribution equality via
   `smul_smul` + commutativity of scalar multiplication
4. `ckaRandExp_eq_ddhExpRand` (`Theorem3.lean`) — distribution equality using
   bijectivity `hg`
5. `ddh_implies_cka_security` (`Theorem3.lean`) — follows from (3) and (4) by
   rewriting the advantage definition
6. `ddh_implies_cka_security_paper_form` (`Theorem3.lean`) — epsilon form by
   instantiating (5)

### Auxiliary restricted-game theorem surface — 1 declaration

7. `ddh_implies_cka_security_delta` (`Theorem3.lean`) — restricted multi-epoch
   `Δ = 1` theorem; follows from the single-epoch reduction plus (2)

### Figure 3 reduction core — 3 declarations

8. `redQueryImpl_preservesRedInv` (`Reduction.lean`) — proves corruption never
   reaches symbolic-secret branches of `stateToConc`
9. `figure3Exp_real_eq_ddhExpReal` (`Reduction.lean`) — real DDH experiment
   equals the real Figure 3 experiment
10. `figure3Exp_rand_eq_ddhExpRand` (`Reduction.lean`) — random DDH experiment
    equals the random Figure 3 experiment

### Figure 3 theorem surface / wrappers — 3 declarations

11. `ddh_implies_figure3_cka_security` (`Theorem3.lean`) — Theorem 3 over the
    full Figure 3 oracle game with `Δ = 1`; the main paper-faithful statement
12. `ddh_implies_cka_security_asymptotic` (`AsymptoticSecurity.lean`) —
    single-epoch asymptotic wrapper via `secureAgainst_of_reduction`
13. `figure3Advantage_le_ddhAdvantage` (`AsymptoticSecurity.lean`) — pointwise
    Figure 3 bound needed by the Figure 3 asymptotic theorem

### Proof strategy

Recommended order:
- First discharge (1): `ddhCKAWithCoins_toCKAScheme` is definitional.
- Then prove the warmup equalities (3) and (4): unfold both sides and show the
  monadic computations produce identical distributions. Key lemmas:
- `smul_smul : (a * b) • x = a • (b • x)` (Module axiom)
- `mul_comm` (Field is commutative)
- `probOutput_map_bijective_uniform_cross` (VCV-io, for bijectivity in (2))
- Then (5), (6), and (7) are short wrapper theorems over the warmup reduction.
- For the Figure 3 layer, prove (8) first: it justifies that corruption never
  exposes symbolic `.aSec` / `.bSec` states.
- With the invariant in place, prove (9) and (10) by relating
  `Reduction.redQueryImpl` to `Figure3.ckaGameQueryImpl`.
- Finally discharge (11) and (13) from the distribution equalities. (12) is the
  single-epoch asymptotic ENNReal lift and should be routine once (5) is in place.

## Runtime Modeling (scaffold complete)

Implemented in `Theorems/AsymptoticSecurity.lean`:
- `ddhSecurityGame` / `ckaSecurityGame` — `SecurityGame` instances indexed by `sp : ℕ`
- `ddh_implies_cka_security_asymptotic` — intended application of `secureAgainst_of_reduction`
- `ckaAdvantage_le_ddhAdvantage_ennreal` — lifts concrete bound to `ℝ≥0∞`
- `isPPT` left abstract (hypothesis); `hreduce` formalizes `t ≈ t'`

Remaining: discharge the admitted wrapper theorem `ddh_implies_cka_security_asymptotic`.

## Figure 3 oracle game (implemented)

Implemented in `CKA/Figure3Game.lean` — paper-faithful oracle-based game:
- `Figure3Adversary` — adaptive `OracleComp` adversary with game oracle access
- `CKAQueryIdx` — oracle index: `sendHonest`, `sendBadRand`, `receive`,
  `challenge`, `corrupt` (all party-specific)
- `ckaOracleSpec` / `ckaGameQueryImpl` — oracle spec and stateful implementation
- All oracle return types wrapped in `Option` — failed `req` guards return `none`
  with state unchanged (paper's rollback semantics, not game-abort)
- `send-P'(r)` checks `allowCorrPostIncrement` (post-increment epoch), matching
  the paper's `t_A++` then `req allow-corr` ordering
- End-of-game tracked via `corruptedPostChalA`/`corruptedPostChalB`; all queries
  return `none` after both parties corrupted post-challenge
- `CKAGameState` — party states, epoch counters, ping-pong phase tracking
- `allowCorrFig3` / `finishedParty` / `corruptionPermittedFig3` — party-specific
  corruption predicates matching Figure 3
- `figure3Exp` / `figure3Advantage` / `Figure3CKASecure` — game and security def
- `CKASchemeWithCoins` in `Defs.lean` — exposes `sendDet` for `send-P'(r)`
- `ddhCKAWithCoins` in `DDHCKA.lean` — DDH-CKA with `SendCoins = F`
- `Reduction.redQueryImpl` / `figure3AdvToDDHAdv` — executable DDH reduction
- `ddh_implies_figure3_cka_security` in `Theorem3.lean` — theorem surface over Figure 3

## Restricted multi-epoch game (auxiliary only)

`CKA/MultiEpochGame.lean` — auxiliary non-adaptive transcript-level model.
NOT the paper-faithful Figure 3 formalization (that is `CKA/Figure3Game.lean`).
- Non-adaptive adversary (commits upfront to `tStar`, epoch count, corruption)
- Corruption not party-specific (no separate `corr-A`/`corr-B`)
- Only sender-side state snapshots tracked
- No bad-randomness oracle (`send-P'(r)` absent)
- `CKASecureDelta` / `ddh_implies_cka_security_delta` target this restricted game

## Figure 3 reduction and asymptotic wrapper (skeleton complete)

`Reduction.lean` / `AsymptoticSecurity.lean` now contain the full Figure 3 reduction scaffold:
- `figure3CkaSecurityGame` — `SecurityGame` instance using `figure3Advantage`
- `figure3AdvToDDHAdv` — executable reduction `(ℕ × Figure3Adversary) → DDHAdversary`
- `redQueryImpl` — symbolic Figure 3 simulator with DDH embeddings at `t* - 1`,
  `t*`, and `t* + 1`
- `figure3Exp_real_eq_ddhExpReal` / `figure3Exp_rand_eq_ddhExpRand` — target
  distribution equalities
- `figure3Advantage_le_ddhAdvantage` — per-adversary pointwise Figure 3 bound
- `ddh_implies_figure3_cka_security_asymptotic` — structurally proved via
  `secureAgainst_of_reduction` + the pointwise bound

Remaining:
- prove `redQueryImpl_preservesRedInv`
- prove `figure3Exp_real_eq_ddhExpReal`
- prove `figure3Exp_rand_eq_ddhExpRand`
- discharge `figure3Advantage_le_ddhAdvantage`
- instantiate those results in `ddh_implies_figure3_cka_security`

## Additional building blocks for the full paper

To formalize the complete double ratchet:
- FS-AEAD (Definition 14, Section 4.2) — forward-secure authenticated encryption
- PRF-PRNG (Definition 16, Section 4.3) — dual-purpose hash function
- SM scheme (Definition 6, Section 3.1) — secure messaging syntax
- SM security game (Figure 2, Section 3.2) — the main security definition
- Theorem 1 (Section 3.3) — correctness + authenticity + privacy ⟹ SM security
- Theorem 6 (Section 5.3) — main composition theorem

## VCV-io dependency decision

See `doc/vcv-io-dependency.md` for analysis. Current decision: keep VCV-io.
Revisit if API friction becomes blocking.

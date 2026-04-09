# DoubleRatchet

Lean 4 formalization of the double ratchet protocol security analysis from:

> Alwen, Coretti, Dodis. "The Double Ratchet: Security Notions, Proofs, and
> Modularization for the Signal Protocol" (2020).

## Current Scope

**Theorem 3** (Section 4.1.2, p22): If group G is DDH-secure, then the
DDH-based Continuous Key Agreement (CKA) scheme is secure with healing
parameter Delta = 1.

This is the core theorem connecting the DDH assumption to CKA security —
the "public-key ratchet" building block of Signal's double ratchet.

Status: **paper-faithful Figure 3 skeleton** — the Figure 3 oracle game now
tracks adaptive queries, ping-pong ordering, party-specific corruption,
bad-randomness oracles, post-increment `allow-corr` for `send-P'(r)`, explicit
end-of-game behavior, and `req` failures as `none` with state unchanged. The
executable DDH reduction lives in `Theorems/Reduction.lean`; proof obligations
are still admitted with `sorry`.

## Project Structure

```
DoubleRatchet/
  CKA/
    Defs.lean              Definition 12: CKAScheme + CKASchemeWithCoins
    SecurityGame.lean      Single-epoch real-or-random game
    Security.lean          Definition 13: CKASecure predicate (single-epoch)
    Figure3Game.lean       Figure 3: adaptive oracle game, Figure3CKASecure with Δ
    MultiEpochGame.lean    Restricted multi-epoch game (auxiliary only, not Figure 3)
  Constructions/
    DDHCKA.lean            DDH-based CKA + ddhCKAWithCoins (Section 4.1.2)
  Theorems/
    Theorem3.lean          Single-epoch warmup + concrete/paper-form/Figure 3 theorem statements
    Reduction.lean         Executable Figure 3 DDH reduction + simulation lemmas/invariant
    AsymptoticSecurity.lean  Single-epoch and Figure 3 SecurityGame wrappers
doc/
  paper-to-lean-correspondence.md   Notation map and 1:1 definition correspondence
  vcv-io-dependency.md              Analysis of VCV-io dependency tradeoffs
  TODO.md                           Sorry proof strategy, remaining work
```

## Dependencies

- **VCV-io** (commit `a3d6c41`): Provides DDH definitions, probability monad
  (`ProbComp`), uniform sampling (`SampleableType`), and probability notation.
  VCV-io transitively brings Mathlib v4.28.0.
- **Lean**: v4.28.0

## Building

```bash
lake exe cache get   # download prebuilt mathlib oleans (required first time)
lake build           # compile — expect sorry warnings, no errors
```

## Future Work

- **Prove the admitted declarations**: 13 local declarations currently use
  `sorry`, spread across `DDHCKA.lean`, `MultiEpochGame.lean`, `Theorem3.lean`,
  `Reduction.lean`, and `AsymptoticSecurity.lean`. See `doc/TODO.md` for the
  current breakdown and proof order.
- **Full paper formalization**: FS-AEAD, PRF-PRNG, SM scheme, Theorems 1/6/8/12
- **VCV-io dependency**: May simplify to direct ZMod p formulation
  (see `doc/vcv-io-dependency.md`)

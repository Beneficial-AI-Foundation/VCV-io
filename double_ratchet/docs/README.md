# DoubleRatchet Documentation Project

Verso-blueprint documentation for the `double_ratchet` Lean 4 formalization.

The docs package mirrors the PQXDH documentation layout:
- a standalone Lake package under `docs/`
- a `Main.lean` rendering entrypoint
- a `Contents.lean` blueprint root
- chapter files under `DoubleRatchetDocs/`
- an optional `SourceBlock.lean` helper for selective proof-source panels

## Dependencies

The docs package depends on:

- `versoBlueprint` pinned to `v4.28.0`
- the parent `DoubleRatchet` package via `path = ".."`

The parent project already brings in VCV-io and Mathlib. The docs package does
not duplicate those dependencies.

## Build

From `double_ratchet/`:

```bash
lake build
lake -d docs update
lake -d docs build DoubleRatchetDocs Main
```

## Render

From `double_ratchet/`:

```bash
lake -d docs env lean --run docs/Main.lean --output docs/_out/site
python3 -m http.server 8000 -d docs/_out/site/html-multi
```

Then open `http://localhost:8000`.

## Current caveat

On this checkout, `lake -d docs build` and `lake -d docs exe docs` try to
build unrelated native `VCV-io` FFI targets whose `third_party` sources are not
present in the docs dependency tree. The targeted `build DoubleRatchetDocs Main`
command and the `lake -d docs env lean --run ...` render command avoid that
issue and are the validated workflow for now.

## Structure

```text
docs/
├── lakefile.toml
├── lean-toolchain
├── Main.lean
├── DoubleRatchetDocs.lean
├── README.md
└── DoubleRatchetDocs/
    ├── Contents.lean
    ├── SourceBlock.lean
    ├── DocIntro.lean
    ├── DocCryptoPrimer.lean
    ├── DocCKA.lean
    ├── DocFigure3.lean
    ├── DocDDHCKA.lean
    ├── DocReduction.lean
    ├── DocTheorem3.lean
    ├── DocAsymptoticSecurity.lean
    └── DocCorrespondence.lean
```

## Content policy

The site is paper-faithful first:
- the canonical surface is Figure 3 in hidden-bit form
- single-epoch and restricted multi-epoch games are documented as auxiliary
- complete definitions are described as authoritative
- admitted theorems are documented as formalized statements with unfinished proofs

# CKA Verso Documentation

Verso/Blueprint documentation for the `Examples/CKA` formalization on the
`cka-and-bisim` branch.

The site is designed as a paper-to-code guide: each major paper object from
ACD19 Section 4.1, Figure 3, and Theorem 3 is presented together with the Lean
declaration that encodes it.

## Build

From the repository root:

```bash
lake -d docs/cka update
lake -d docs/cka exe cache get
lake -d docs/cka build CKADocs Main
```

## Render

From the repository root:

```bash
lake -d docs/cka env lean --run docs/cka/Main.lean --output docs/cka/_out/site
python3 -m http.server 8000 -d docs/cka/_out/site/html-multi
```

Then open `http://localhost:8000`.

The docs import the live `Examples.CKA` modules. If a Lean declaration is
renamed or removed, the documentation build should fail rather than silently
drift.

Avoid `lake -d docs/cka build docs` on checkouts without the vendored native
`third_party` FFI sources. Building the executable links the root package's
extern libraries; `lake -d docs/cka build CKADocs Main` and `lean --run` avoid
that link step.

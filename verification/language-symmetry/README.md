# Focused language-symmetry verification

This Lake project compiles the actual files under `../../lean`, including the
existing Peirce compression owner. It uses the root project's exact Lean
`v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins.
It does not require the root project's unrelated local dependency checkouts.

From the repository root, with the pinned Lean toolchain available:

```sh
python3 verification/language-symmetry/check.py exe cache get
python3 verification/language-symmetry/check.py build InfoGeometry.LLM.LanguageSymmetryRepresentationGeometryAudit --wfail
```

The first command is only needed when the pinned Mathlib cache is absent.
`check.py` uses the maintained repository build lock and workspace integrity
checks, and retains the lock until its Lake child has exited. It does not alter
the root manifest, root Lake configuration, or toolchain.

The audit module prints axiom dependencies for every public declaration in the
six new mathematical modules. Inspect the output: only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. A successful command is a
focused source-and-dependency check, not a certificate for the full LLM umbrella
or the root default targets.

For an explicit file recheck, pass an absolute source path:

```sh
python3 verification/language-symmetry/check.py env lean /absolute/repository/lean/InfoGeometry/LLM/LanguageSymmetryRepresentationGeometryAudit.lean
```

The mathematical contract, corrections to the intake, and observed validation
results are in [`docs/LANGUAGE_SYMMETRY_FORMALIZATION.md`](../../docs/LANGUAGE_SYMMETRY_FORMALIZATION.md).

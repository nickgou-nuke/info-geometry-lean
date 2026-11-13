# Hilbert localization: reproducible verification

## Exact scope

The proposed owners are:

- `InfoGeometry.Analysis.HilbertLocalization`
- `InfoGeometry.Analysis.HilbertLocalizationEnergy`
- `InfoGeometry.Analysis.HilbertGramDuality`

Their repository source closure contains these three modules plus six
unchanged dependencies. Mathlib remains pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean to `v4.34.1`.
The [theorem contract](../../docs/HILBERT_LOCALIZATION_GRAM_CONTRACT.md)
states the carriers, hypotheses, existing owners, and remaining analytic work.

## Current status

Independent mathematical and owner-reuse review passed. The initial six
dependency modules compiled; unchanged `Core.PeirceDecomposition` emitted one
`unnecessarySeqFocus` style warning. An isolated development import-path issue
was corrected by placing the freshly compiled dependency artifacts in the
same module root as the candidates.

The initial energy-module check found one final simplification mismatch and
two style warnings. Repairs are present. The repaired owner checks and final
native axiom audit are pending in the shared local build queue. This record
does not certify the new modules as kernel accepted yet.

The dedicated [GitHub workflow](../../.github/workflows/hilbert-localization.yml)
checks the exact proposed head revision on an independent runner. Its success
requires fresh compilation of the complete repository source closure,
zero warnings in all three new owners, native auditing of every owned
declaration, strict placeholder and semantic screening, and matching source
hashes. Its evidence artifact contains the source-closure report, native
axiom log, generated audit source, semantic report, and SHA-256 manifest.

## Local reproduction

Use an independently initialized Mathlib checkout at the exact repository
pin and the pinned Lean executable. Set `HILBERT_MATHLIB_ROOT`,
`HILBERT_LEAN`, and `HILBERT_REPORT_DIR` to those paths and a fresh output
directory, then run from the repository root:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root "$HILBERT_MATHLIB_ROOT" \
  --lean "$HILBERT_LEAN" \
  --output "$HILBERT_REPORT_DIR" \
  --target InfoGeometry.Analysis.HilbertLocalization \
  --target InfoGeometry.Analysis.HilbertLocalizationEnergy \
  --target InfoGeometry.Analysis.HilbertGramDuality
```

The maintained checker verifies the pins, copies the exact source closure,
uses the shared build lock, and audits native declaration ownership and
axiom dependencies. Use a fresh output directory; do not pass
`--incremental` or `--skip-audit` for acceptance.

For these explicit targets, also inspect `report.json` and require all three
target warning counts to be zero. The checker's built-in warning rejection
is specific to its original Clifford-Dirac prefix; the dedicated workflow
therefore makes this additional assertion explicitly.

Run the ordinary root-project check separately:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Analysis.HilbertLocalization \
  InfoGeometry.Analysis.HilbertLocalizationEnergy \
  InfoGeometry.Analysis.HilbertGramDuality
```

The root project has additional dependency and gate obligations. A focused
source-closure result does not certify every repository target, and a
workflow's name or presence is not evidence that it ran successfully.

## Mathematical boundary

The arbitrary-Hilbert localization, rectangular leakage, conditional energy
bound, and native Gram eigenspace transport are the intended theorem scope.
The geometric loss estimate, Gaussian transforms, Fock subaveraging, and
infinite Gabor sampling remain separate obligations. No proof of the full
analytic fractal uncertainty principle is asserted by this check.

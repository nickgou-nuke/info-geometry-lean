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

## Verification evidence

The first dedicated [CI run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43385697633)
checked revision `722d3235ce9a310830d5fd84e3ab7b9d8b24651e`.
All nine repository closure modules compiled freshly, and the native audit
checked 87 declarations owned by the three new modules: 58 localization,
6 energy, and 23 Gram-duality declarations. Their only axiom dependencies
were `propext`, `Classical.choice`, and `Quot.sound`. Strict placeholder and
source screening passed; semantic screening reported zero errors and five
reviewed direct-identity warnings.

That run did not pass the final acceptance gate: the localization owner
emitted one `unnecessarySimpa` warning. The zero-power proof now uses `simp`
directly. The unchanged dependency `Core.PeirceDecomposition` separately
emitted one `unnecessarySeqFocus` warning; it is not a new-owner warning.
The zero-warning gate remains enabled.

The initial evidence artifact is `14017824393`; its downloaded ZIP was
independently checked against SHA-256
`765b1ebb7257424c445a7cfbbd62acb2ab65dc8b91e261fad51453c8ae16ba7b`.
Independent mathematical and owner-reuse review also covered the proposed
source files. The latest run attached to [PR #346](https://github.com/nickgou-nuke/info-geometry-lean/pull/346)
is the authoritative acceptance result for its exact head; the earlier
compiler success alone does not certify a later revision.

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

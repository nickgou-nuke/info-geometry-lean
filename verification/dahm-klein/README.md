# Focused verification of the Dahm exterior Klein action

This project compiles the canonical repository files under `../../lean` using
Lean `v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All nine effective Git dependency revisions match the root manifest. Root
dependency and toolchain files are unchanged.

From the repository root, with the pinned Lean tools on `PATH`:

```bash
python3 verification/dahm-klein/check.py exe cache get
python3 verification/dahm-klein/check.py build
python3 verification/dahm-klein/check.py env lean \
  "$PWD/lean/InfoGeometry/Projective/ExteriorKleinOperatorAudit.lean"
python3 tools/infra/opengauss_screener.py --strict \
  lean/InfoGeometry/Projective/ExteriorKleinOperatorAction.lean \
  lean/InfoGeometry/Projective/ExteriorKleinDeterminantCovariance.lean \
  lean/InfoGeometry/Projective/ExteriorKleinOperatorExamples.lean \
  lean/InfoGeometry/Projective/ExteriorKleinBoost.lean \
  lean/InfoGeometry/Projective/ExteriorKleinIncidenceAction.lean
```

`check.py` uses the maintained workspace-integrity checks and shared build lock.
It rejects linked Git worktrees and symlinked Lake roots. Do not run concurrent
compiler checks, update pins, or delete caches. Existing canonical imports
include the Mathlib umbrella transitively; consequently the first build/cache
retrieval has a larger dependency footprint than the new source files alone.

The audit selects every declaration owned by the five mathematical modules,
including generated declarations. It rejects introduced axioms, unsafe/partial
declarations, and transitive axioms outside `propext`, `Classical.choice`, and
`Quot.sound`. The output lists each checked name and its axiom footprint.
Generated theorem declarations count separately from named source theorems.

This is finite-dimensional real exterior algebra with full noncommutative
endomorphism composition. Read the [theorem contract](../../docs/DAHM_KLEIN_OPERATOR_ACTION_CONTRACT.md)
for source provenance, dependency order, and physical/projective scope limits.

This focused project does not initialize the root's unrelated optional path
dependencies, certify all root targets, or replace the root pre-push gate.
Verification results and any root integration blocker are recorded separately
in [RESULTS.md](RESULTS.md). Independent acceptance applies only to its recorded
source fingerprint. The earlier lost checkout's acceptance is not reused.

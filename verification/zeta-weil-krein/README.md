# Focused finite arithmetic and compatible colimit verification

This project compiles the changed theorem owners and their repository imports
against the root project's unchanged Lean and Mathlib pins. It provides a
focused check; it does not replace the repository's root build or push gate.

## Inputs

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All nine dependency URL/revision pairs agree with the root manifest.
- Sources are read from `../../lean`; dependencies from `../../.lake/packages`.
- Build outputs remain local to this verification project.
- The two audit entry points determine the checked repository import closure;
  the build does not certify unrelated modules.

## Reproduce

From the repository root, with the pinned toolchain and its dependency cache
available, use the maintained shared-lock wrapper:

```bash
python3 verification/zeta-weil-krein/check.py --wfail build \
  InfoGeometry.Arithmetic.ZetaDihedralWeilKreinAudit \
  InfoGeometry.Categorical.CompatibleColimitAudit
```

The original audit includes two arithmetic examples and 52 `#print axioms`
commands: its original 46 declarations plus six dependency lemmas repaired for
warning-free validation. The colimit audit adds 24 disjoint declarations,
covering every public declaration in its three implementation owners and the
four radical-map lemmas. The checker requires all 76 records, each exactly once.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted foundations.
The checker rejects missing or duplicate records and every axiom outside the
allow-list. Printing the dependencies alone does not enforce this requirement.

For fresh output independent of Lake's replayed build messages, use the focused
runner. It validates the focused/root pins and holds the same shared build lock:

```bash
set -euo pipefail
mkdir -p verification/zeta-weil-krein/logs
python3 verification/zeta-weil-krein/check.py env lean \
  lean/InfoGeometry/Arithmetic/ZetaDihedralWeilKreinAudit.lean \
  2>&1 | tee verification/zeta-weil-krein/logs/axioms.log
python3 verification/zeta-weil-krein/check.py env lean \
  lean/InfoGeometry/Categorical/CompatibleColimitAudit.lean \
  2>&1 | tee verification/zeta-weil-krein/logs/colimit-axioms.log
python3 verification/zeta-weil-krein/check_axioms.py \
  verification/zeta-weil-krein/logs/axioms.log \
  verification/zeta-weil-krein/logs/colimit-axioms.log
```

On a clean checkout with missing pinned Mathlib artifacts, the corresponding
cache command is `python3 verification/zeta-weil-krein/check.py exe cache get`.
The workflow `.github/workflows/zeta-weil-krein.yml` screens thirteen explicit
owners, builds both audits with warnings treated as errors, captures fresh axiom output,
enforces the allow-list, and uploads the checked revision and logs. It checks
the exact PR head. Hosted results remain separate from local source review.

The theorem contracts and compatibility notes are in
`docs/ZETA_WEIL_KREIN_STOKES_CONTRACT.md` and
`docs/COMPATIBLE_COLIMIT_CONTRACT.md`. Compiler output and independent QA
must be assessed separately from the source-level screens. No RH/GRH theorem,
global Weil positivity theorem, analytic heat-kernel limit, or completed
Hilbert-space construction is asserted by this project.

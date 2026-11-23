# Focused zeta, Weil–Krein and finite Stokes verification

This project compiles the changed theorem owners and their repository imports
against the root project's unchanged Lean and Mathlib pins. It provides a
focused check; it does not replace the repository's root build or push gate.

## Inputs

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- All nine dependency URL/revision pairs agree with the root manifest.
- Sources are read from `../../lean`; dependencies from `../../.lake/packages`.
- Build outputs remain local to this verification project.
- The audit import closure contains seventeen repository modules.

## Reproduce

From the repository root, with the pinned toolchain and its dependency cache
available, use the maintained shared-lock wrapper:

```bash
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock --wfail \
  InfoGeometry.Arithmetic.ZetaDihedralWeilKreinAudit \
  -- --dir=verification/zeta-weil-krein
```

The audit includes two arithmetic examples and forty-six `#print axioms`
commands: the thirty-seven new named declarations, six modified existing
supertrace declarations, and three reused arithmetic/reflection declarations.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted foundations.
After capturing the complete compiler output, check every reported declaration:

```bash
python3 verification/zeta-weil-krein/check_axioms.py /path/to/focused-build.log
```

The checker rejects missing or duplicate records and every axiom outside the
allow-list. Printing the dependencies alone does not enforce this requirement.

For fresh output independent of Lake's replayed build messages, use the focused
runner. It validates the focused/root pins and holds the same shared build lock:

```bash
python3 verification/zeta-weil-krein/check.py env lean \
  lean/InfoGeometry/Arithmetic/ZetaDihedralWeilKreinAudit.lean
```

On a clean checkout with missing pinned Mathlib artifacts, the corresponding
cache command is `python3 verification/zeta-weil-krein/check.py exe cache get`.
The workflow `.github/workflows/zeta-weil-krein.yml` screens the six changed
owners, builds with warnings treated as errors, captures fresh axiom output,
enforces the allow-list, and uploads the checked revision and logs. It checks
the exact PR head. Hosted results remain separate from local source review.

The theorem contract and compatibility notes are in
`docs/ZETA_WEIL_KREIN_STOKES_CONTRACT.md`. Compiler output and independent QA
must be assessed separately from the source-level screens. No RH/GRH theorem,
global Weil positivity theorem, analytic heat-kernel limit, or completed
Hilbert-space construction is asserted by this project.

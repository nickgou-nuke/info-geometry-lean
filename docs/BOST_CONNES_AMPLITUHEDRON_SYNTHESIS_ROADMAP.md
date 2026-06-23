# Bost-Connes / Amplituhedron Synthesis Roadmap

This note is the placement guide for the proposed synthesis lane.  The current
repository should treat the connection as a conditional comparison interface,
not as a proved equality between the Riemann zeta partition function and an
all-loop `N = 4` SYM integrand.

## Stable Lean Surface

- `InfoGeometry.Projective.BostConnesAmplituhedronSynthesis.synthesis_readout_of_explicit_comparison`
  records the only safe first bridge: a geometry readout follows from an
  explicit comparison equality.
- `InfoGeometry.Projective.BostConnesAmplituhedronSynthesis.synthesis_readout_trans`
  composes comparison readouts, suitable for a future chain
  `partition data -> cohomology boundary data -> amplituhedron data`.
- `InfoGeometry.Projective.BostConnesAmplituhedronSynthesis.arnold_kernel_synthesis_boundary_zero`
  reuses the Arnold kernel premise as a zero boundary readout in a target
  semiring.

## Placement

- Arithmetic/zeta owners belong under `lean/InfoGeometry/Algebra/` or
  `lean/InfoGeometry/Arithmetic/`.
- Twistor, Arnold, Rohozhkin, and amplituhedron comparison owners belong under
  `lean/InfoGeometry/Projective/`.
- The synthesis interface lives at
  `lean/InfoGeometry/Projective/BostConnesAmplituhedronSynthesis.lean`.

## Required Assumptions For Any Stronger Claim

- A precise analytic partition object, including domain, convergence, branch,
  and regularization choices.
- A precise amplituhedron or positive-Grassmannian integrand object.
- A comparison map from arithmetic partition data to cohomological boundary
  data.
- A comparison map from cohomological boundary data to amplituhedron integrand
  data.
- A theorem that these maps preserve the structures being cited: residues,
  factorization channels, symmetries, and normalization.

## Open Debt

- No theorem currently proves `zeta = all-loop integrand`.
- No theorem currently proves the Bost-Connes KMS state is a geometric integral
  over the quadric complement.
- No theorem currently proves the Arnold mixed relation is BCFW recursion.
- No theorem currently proves the rank-32 candidate is an `N = 4` SYM
  supermultiplet.
- No theorem currently proves Rohozhkin/Delaunay flips are plabic graph square
  moves.

## Verification

Use:

```bash
lake env lean lean/InfoGeometry/Projective/BostConnesAmplituhedronSynthesis.lean
lake build InfoGeometry.Projective.BostConnesAmplituhedronSynthesis
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Projective.All
rg -n "sorry|sorryProof|admit|axiom|_True|_valid|_certificate|_law|law_holds|recovery_law" \
  lean/InfoGeometry/Projective/BostConnesAmplituhedronSynthesis.lean \
  docs/BOST_CONNES_AMPLITUHEDRON_SYNTHESIS_ROADMAP.md
```

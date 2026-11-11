# Plücker complex and Peirce verification

This package checks the exact owners under `lean/InfoGeometry/Projective/`:

- `PluckerLinearComplex.lean`: the alternating form, Pfaffian discriminant,
  nondegeneracy and polar hyperplanes.
- `PluckerLinearComplexGeometry.lean`: actual two-plane membership, the
  special-complex directrix and exact radical.
- `PluckerComplexPencil.lean`: homogeneous pencil equations, congruence
  preservation and conditional directrices of real special members.
- `PluckerQuadraticComplex.lean`: native quadratic forms on the existing
  exterior square, projective complex invariance and polar reciprocity.
- `PluckerPeirceBracket.lean`: ordered ring-valued corner composition,
  matrix-unit realization and compatibility with the existing Klein equation.
- `PluckerLinearComplexAudit.lean`: all public declaration axiom dependencies
  and zero/characteristic-two/no-real-root boundary examples.

The package uses the parent source directory directly. It preserves Lean
`v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Dependencies live in the parent checkout's ordinary `.lake/packages`
directory; no symlinked workspace or duplicate theorem sources are needed.
It does not require the root package's optional external projects.

From the repository root:

```sh
python3 verification/plucker-complex/check.py exe cache get
python3 verification/plucker-complex/check.py build
python3 verification/plucker-complex/check.py env lean \
  lean/InfoGeometry/Projective/PluckerLinearComplexAudit.lean
```

The wrapper holds the existing repository-wide build lock. The supplied
manifest fixes dependency revisions; these commands do not call `lake update`.
The cache command is needed only when the pinned artifacts are absent.

The first mathematical source contract is
[`PLUCKER_LINEAR_COMPLEX_CONTRACT.md`](../../docs/PLUCKER_LINEAR_COMPLEX_CONTRACT.md).
A focused pass certifies these source files and their actual import closure.
It does not certify the unrelated root default targets or replace a required
publication gate.

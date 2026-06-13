# Kashiwara-Cuntz Cohomology Index

> Owner: `lean/InfoGeometry/Canonical/KashiwaraCuntzCohomology.lean`
>
> SymPy witness: `tools/sympy/kashiwara_cuntz_cohomology.py`

This index records the finite proof strength of the Kashiwara/Cuntz boundary
layer.

## Closed Lean Content

The Lean module proves a symbolic binary-word calculus:

- `lowerLeft` and `lowerRight` prefix a finite Cantor/crystal word.
- `raiseLeft` and `raiseRight` partially delete a matching head bit.
- Matching raising after lowering recovers the original word.
- The empty word is annihilated by both raising maps.
- `mirror` is involutive and swaps left/right branch conventions.
- `finite_kashiwara_cuntz_cohomology_packet` collects those finite identities.

## SymPy Witness

The SymPy script checks the same identities over all binary words up to a fixed
depth and verifies the truncated matrix identity `R_b * L_b = I` on the source
block whose lowered image remains inside the cutoff.

## Not Proved Here

This is not a proof of:

- Hilbert-space Cuntz adjoints or a concrete `O₂` representation;
- `K_0(O₂) = 0` or `K_1(O₂) = 0`;
- full Kashiwara crystal bases;
- Weyl character integrability;
- an `E₈(8)` Jordan triple system;
- analytic zeta, Katz-Sarnak, or RH consequences.

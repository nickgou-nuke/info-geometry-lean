# Klein Quadric / Motive-Driven Monodromy Bridge

This note tracks the practical “stepping-stone” formalization: computational checks in
SymPy/Sage/GAP/galgebra/Clifford and Lean 4 theorems around the Klein-quadric
log-potential.

## 1) What is formalized in Lean today

The core file is:
- `lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean`

Currently established lemmas include:
- `circleIntegral_one_div` : `∮ (1/z) dz = 2πi` on a circle
- `deRhamClass_of_winding` and `wilsonPhase_of_winding`
- `chiralNullConductor_eq_selfOrthogonal` : `kleinPotential P = 0 ↔ Plucker6.polar P P = 0`
- `universalCoverLog_sheet_increment`
- `negLogDerivative_at`
- `chiralDetPotential_eq_zero_iff` (new in `KleinQuadricGrothendieckDeRham.lean`) : factorization of the determinant-style potential

These are lightweight but capture the local monodromy statement on `C*` and the
chiral null-cone classification relation in projective language.

## 2) Multi-backend computational bridge

Run:

```bash
python3 formalizations/klein_quadric_motive_bridge.py
```

Blocks:
- SymPy: Klein potential, Grothendieck–de Rham toy identity `dQ/Q`, residue circle integral,
  tripotent idempotent check.
- GAP: polar Gram form (rank/determinant/nullity) in Plücker coordinates.
- Sage: degree/Jacobian rank/gradient ideal singular dimension for
  `f = q(a) q(b) q(a-b)`.
- galgebra: signature-2/4-vector toy geometric checks.
- Clifford: blade basis + tripotent check where available.
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive` file adds Tomita-sheet transport and Wilson-Holonomy lemmas on top of `uLog` and `1/z` winding.
- Macaulay2: startup + package load check (`Dmodules`, `BernsteinSato`).
- `compute_derham.m2`: high-fidelity Oaku/Dlocalize + `rationalFunctionExt` witness for the 8-variable `f=q(a)q(b)q(a-b)` (heavy, background/manual run).
- Track-B helper:
  `python3 formalizations/compute_derham_track_b.py --launch --watch --log /tmp/compute_derham.out`

For heavy Grothendieck–de Rham computations (true deRham rank/cohomology of the
full 8-variable complement), Macaulay2 may require longer runtimes; use the
system `M2` directly when needed.

## 3) Runtime status in this repo

- `M2` (system) is available and `deRham` works on toy polynomials.
- Full 8-variable `deRham f` may still be expensive; failures here are often
  timeout/resource-related rather than installation-related.

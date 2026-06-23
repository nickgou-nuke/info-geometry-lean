# Klein Quadric Time-Cohomology Roadmap

**Status:** local logarithmic/de Rham corridor verified; global physical-time theorem remains debt  
**Date:** 2026-06-18  
**Primary Lean owners:**

- `lean/InfoGeometry/Projective/KleinQuadricTime.lean`
- `lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean`
- `lean/InfoGeometry/Projective/KleinQuadricGrothendieckDeRham.lean`

This note packages the theorem-safe version of the statement:

```text
time is represented by the logarithmic de Rham winding class around the
Klein-quadric divisor
```

The current repository proves local algebraic, residue, monodromy, and
log-barrier readouts.  It does not yet prove a global theorem identifying
physical time, Tomita-Takesaki modular flow, Berry holonomy, or spacetime
causality with this de Rham class.

## Source Artifact

Local PDF pointer:

```text
/home/goutev/Downloads/collection_for_formalization/thesis.pdf
```

PDF metadata identifies it as:

```text
Konrad Voelkel, "Motivic Cell Structures for Projective Spaces over Split
Quaternions", PhD Thesis, March 2016.
MSC2010: 14F42, 17A75, 20Gxx.
```

This source is relevant to split-composition/projective/motivic cell-structure
background.  It is not a Lean theorem owner and is not treated as closing the
Klein time-cohomology theorem.

## Stable Lemma Surface

### Plucker/Klein Algebra

Owner: `lean/InfoGeometry/Projective/KleinQuadricTime.lean`

- `InfoGeometry.Projective.KleinQuadric.Plucker6.coordinatePairing_kleinGradient_eq_polar`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinQ_add_scale`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.polar_symm`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.polar_self_eq_two_mul_kleinQ`

Meaning: the coordinate gradient, polar form, and quadratic Taylor expansion of
the Klein form are algebraically proved in Lean.

### Log-Barrier Hessian

Owner: `lean/InfoGeometry/Projective/KleinQuadricTime.lean`

- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_symm`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_self`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_radial_left`
- `InfoGeometry.Projective.KleinQuadric.Plucker6.kleinBarrierHessian_radial_self`

Meaning: the bilinear Hessian expression for the formal barrier `-log(Q)` is
kernel-checked, including radial contraction readouts.  Full
self-concordance inequalities are not proved.

### Tripotent And Null-Projection Algebra

Owner: `lean/InfoGeometry/Projective/KleinQuadricTime.lean`

- `InfoGeometry.Projective.KleinQuadric.Time.tripotent_fourth_eq_square`
- `InfoGeometry.Projective.KleinQuadric.Time.tripotent_square_idempotent`
- `InfoGeometry.Projective.KleinQuadric.Time.nullSpaceProjection_idempotent`
- `InfoGeometry.Projective.KleinQuadric.Time.nullSpaceProjection_mul_tripotent_eq_zero`
- `InfoGeometry.Projective.KleinQuadric.Time.tripotent_mul_nullSpaceProjection_eq_zero`

Meaning: if `T^3 = T`, then `T^2` and `1 - T^2` have the expected finite
projection behavior.  This is algebraic tripotent calculus, not a geometric
classification of all null boundary fields.

### Logarithmic Form And Winding

Owners:

- `lean/InfoGeometry/Projective/KleinQuadricGrothendieckDeRham.lean`
- `lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean`
- `lean/InfoGeometry/Projective/KleinQuadricTime.lean`

Stable theorem names:

- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckLog_deriv_log`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckLog_deriv_neg_log`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.circleIntegral_grothendieck_dlog`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckWinding_of_sheet`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.tomita_sheet_transport`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMotive.grothendieckTomitaWilsonBridge`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.circleIntegral_one_div`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.deRhamClass_of_winding`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.wilsonPhase_of_winding`
- `InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy.chiralNullConductor_eq_selfOrthogonal`
- `InfoGeometry.Projective.KleinQuadric.Time.timeCohomology_eq_two_pi_I`
- `InfoGeometry.Projective.KleinQuadric.Time.timeCohomology_exp_eq_one`
- `InfoGeometry.Projective.KleinQuadric.Time.timeCohomology_eq_circleIntegral_grothendieck_dlog`

Meaning: the local model `dz/z`, its `2*pi*i` period, integer winding phase,
universal-cover sheet increment, and the named `timeCohomologyWinding` readout
are proved.  This is the verified local/logarithmic corridor.

## SymPy/GAP/Sage/Clifford Evidence

Owner: `formalizations/chiral_causal_cone_time_witness.py`

Current witness blocks check:

- symbolic `dQ/Q` and `d(-log Q) = -dQ/Q`;
- gradient/polar and Taylor identities;
- barrier Hessian bilinear formula and radial contractions;
- `∫ dz/z = 2*pi*i` on the unit circle;
- optional GAP tripotent projection checks;
- optional Sage irreducibility/Euler homogeneous identity;
- optional `galgebra`/`clifford` null and tripotent checks.

These are companion evidence only.  Lean owner files decide theorem status.

## Assumptions Needed For The Next Lane

- A precise global space: the complement of the Klein divisor with stated
  topology, smooth/analytic structure, and branch-cover conventions.
- A real de Rham cohomology computation proving the relevant `H^1` generator,
  not only the local `dz/z` residue model.
- A representation theorem connecting the scalar logarithmic class to the
  chiral causal algebra or operator-algebraic boundary model.
- A Tomita-Takesaki modular-flow theorem linking the represented logarithmic
  class to an implemented modular operator `Delta` and its generator.
- A Berry/Wilson holonomy theorem over a concrete connection, not only a scalar
  exponential phase identity.
- Analytic self-concordance inequalities for the Klein barrier, if the
  interior-point/information-geometry interpretation is promoted to theorem
  status.

## Open Debt

- `D1`: Formalize the global Klein-divisor complement and compute its relevant
  de Rham class, or import a certified theorem with exact hypotheses.
- `D2`: Replace local `dz/z` circle residue readbacks by a theorem that pulls
  back `dQ/Q` along an explicit tubular loop around the Klein divisor.
- `D3`: Prove analytic self-concordance inequalities for `-log(Q)` on the
  chosen causal/symmetric cone domain.
- `D4`: Construct the modular operator/flow owner needed to state
  `Delta^{it}` and prove compatibility with the logarithmic class.
- `D5`: Build the Berry/Wilson connection theorem and show its holonomy is the
  same integer-winding class under explicit premises.
- `D6`: State any physical-time theorem only as a final interface over `D1` to
  `D5`; do not infer it from the local monodromy lemmas alone.

## Verified Commands

```bash
lake env lean lean/InfoGeometry/Projective/KleinQuadricTime.lean
lake env lean lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean
lake env lean lean/InfoGeometry/Projective/KleinQuadricGrothendieckDeRham.lean
python3 formalizations/chiral_causal_cone_time_witness.py
```

# Represented density exponential v3: reusable proof decomposition

Author: Popper. New sandbox only; v1/v2 and all live owners preserved.
Source: FiniteSeedRepresentedDensityExponential20261024v3.lean.
Uncompiled. Independent AA and serialized QA required. No acceptance inferred
from the decomposition; v2's instance-alignment repair remains unverified.

## Six named mathematical lemmas

- map_gibbsDensity_eq_cfc: actual finite Hermitian CFC transport through a
  complex star algebra hom f into a genuine CStarAlgebra A. Uses the real
  restriction of that same f and derived finite-dimensional continuity.
- cfc_expWeight_eq_exp: for any actual self-adjoint G in A, evaluate the
  native weight r ↦ Real.exp(-beta*r) as exp((-beta) • G), using CFC scaling.
- map_gibbsDensity_eq_exp: compose the two previous results; self-adjointness
  of f H follows from map_star and hH, never an extra hypothesis.
- map_gibbsDensityUnit_inv_eq_exp: unchanged v2 proof of inverse uniqueness,
  with NormedAlgebra ℚ A derived by restriction from ℂ.
- representedDensityUnit_coe_eq_exp and representedDensityUnit_inv_coe_eq_exp:
  unchanged actual native seedStageHom/representedDensityUnit specializations.

## Precise instance alignment

The native complex target CFC and its real restriction are named LOCAL instance
choices in section DensityCFC, before the three helper/main statements elaborate.
Thus the CFC middle term in both helpers and their composition uses the same
choice, not a caller-supplied CFC or desired equality. Source matrix CFC remains
explicit Matrix.IsHermitian.instContinuousFunctionalCalculus inside transport.
The map_cfc invocation fixes R=S=ℝ and fR=f.restrictScalars ℝ, as in v2.
The public helpers require only CStarAlgebra A (plus finite matrix data where
applicable); no CFC or scalar-continuity premise is added to the intended contract.
QA must inspect actual elaborated signatures and generated local-instance heads.

All four v2 mathematical statements and the inverse/concrete proof bodies remain
unchanged; two reusable helpers are added. Section binders factor the same target
A/CStarAlgebra assumptions. No raw-matrix NormedRing, new carrier/state/density,
budget increase, transparency setting, strip wrapper or analytic claim.
All real beta remain allowed. Density is the unnormalized existing Gibbs unit.

Native grounding remains the v2 contract: FiniteMatrixGibbsFunctional,
FiniteSeedRepresentedRealTime, map_cfc finite-dimensional continuity pattern,
Mathlib cfc_comp_const_mul, CFC.real_exp_eq_normedSpace_exp, exponential
addition and Units.inv_eq_of_mul_eq_one_right. This is only analytic-KMS
research step 1, not the later complex-time extension or strip bound.

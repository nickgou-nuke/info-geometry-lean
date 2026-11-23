/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.FiniteEulerLogDerivative
import InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore
import InfoGeometry.LinearAlgebra.PositiveRadicalQuotient
import InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
import InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes
import InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge
import InfoGeometry.Arithmetic.ZetaDihedral

/-!
# Declaration audit for the real reflection, finite Euler and quotient core

This audit also imports the existing actual zeta logarithmic derivative and
critical-reflection owners. Their analytic statements retain their original
complex chart, while the new reflection and pairing core is real or generic.
The audit does not assert the Weil positivity criterion or GRH.
-/

open scoped LSeries.notation
open ArithmeticFunction

-- Exact prime-power weights used in the finite expansion.
example {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

-- The native generalized-character identity is already analytic for Re(s)>1.
example {N : ℕ} (chi : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L (↗chi * ↗Λ) s = -deriv (L ↗chi) s / L ↗chi s :=
  DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs

#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.units_logDeriv_mul
#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.units_logDeriv_inv
#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.units_logDeriv_prod
#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.negative_units_logDeriv_eulerFactor
#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.negative_units_logDeriv_eulerProduct
#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.one_sub_mul_sum_powers
#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.negative_units_logDeriv_eulerFactor_eq_sum_add_remainder
#print axioms InfoGeometry.Arithmetic.FiniteEulerLogDerivative.negative_units_logDeriv_eulerProduct_eq_sum_add_remainder
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.anticommute_of_reflection
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.reflection_eigen_equation
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.reflection_hasEigenvector
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.reflection_law_allows_positive_real_eigenvalue
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.critical_reflection_fixed_iff
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.spectral_negation_fixed_iff
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.coordinate_sheets_isotropic
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.diagonal_cross_pairing
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.antidiagonal_cross_pairing
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.cross_pairing_has_both_signs
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.negative_pair_of_remainder_bound
#print axioms InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.not_nonneg_cross_pairing_pullback
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm_mk
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm_symm
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm_isSymm
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm_nonneg
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm_nonneg_iff
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.quotientForm_self_eq_zero_iff
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.negative_survives_radical_quotient
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.innerProductCore
#print axioms InfoGeometry.LinearAlgebra.PositiveRadicalQuotient.innerProductCore_inner_mk
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.supertrace_pow_succ_eq_zero
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.supertrace_polynomial_eq_constant
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.supertrace_eq_zero_of_odd
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.odd_mul_positiveProjector_eq_negativeProjector_mul
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.odd_mul_negativeProjector_eq_positiveProjector_mul
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.positiveToNegativeDifferential_eq
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.negativeToPositiveDifferential_eq
#print axioms InfoGeometry.OperatorAlgebra.FiniteParitySupertrace.restrictedDifferentials_comp_zero
#print axioms InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes.vertexCurvature
#print axioms InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes.incidence_curvature_sum
#print axioms InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes.cellCirculation
#print axioms InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes.rectangular_stokes
#print axioms InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes.cellCirculation_exact

#print axioms InfoGeometry.Arithmetic.ActualRiemannZetaVonMangoldtBridge.actualRiemannZetaLogDerivative_eq_vonMangoldt_LSeries
#print axioms InfoGeometry.Arithmetic.ZetaDihedral.critical_line_is_invariant_orbit
#print axioms DirichletCharacter.LSeries_twist_vonMangoldt_eq

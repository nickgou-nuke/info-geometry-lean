/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LinearAlgebra.TraceAnticommutation
import InfoGeometry.OperatorAlgebra.ZornMajoranaGradedCurvature
import InfoGeometry.Algebra.Zorn.SplitOctonionDerivationConjugation

/-!
# Native supertrace cancellation with nonzero Zorn operator curvature

The trace is `LinearMap.trace` on the actual finite-dimensional Zorn module.
The grading, charge and curvature remain full endomorphisms. Its vanishing
scalar readout is paired with the established noncentral, non-flat operator
identities, without introducing a trace backend or a scalar replacement.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ZornMajoranaSupertrace

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix (left_diagonal_difference_involution)
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.OperatorAlgebra.ZornMajoranaGradedCurvature
open InfoGeometry.LinearAlgebra.TraceAnticommutation

/-- Cyclicity kills the parity-weighted square. Only anticommutation is needed. -/
theorem trace_mul_square_eq_zero_of_anticommute
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Γ Q : Module.End ℝ V) (h : Γ * Q + Q * Γ = 0) :
    LinearMap.trace ℝ V (Γ * (Q * Q)) = 0 := by
  have hanti : (Γ * Q) * Q + Q * (Γ * Q) = 0 := by
    calc
      (Γ * Q) * Q + Q * (Γ * Q) = (Γ * Q + Q * Γ) * Q := by
        noncomm_ring
      _ = 0 := by rw [h, zero_mul]
  simpa only [mul_assoc] using
    linearMap_trace_mul_zero_of_anticommute (Γ * Q) Q hanti

/-- Finite dimension follows from two existing actual coordinate equivalences. -/
local instance : FiniteDimensional ℝ (ZornVectorMatrix ℝ) := by
  let e := nativeCanonicalVectorLinearEquiv.symm.trans
    (InfoGeometry.Canonical.ZornMatrix.coordLinearEquiv (R := ℝ))
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

theorem higherOddCharge_supertrace_zero :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ)
      (leftGrading * (higherOddCharge * higherOddCharge)) = 0 := by
  have hΓ : (leftGrading : ZornOp ℝ) * leftGrading = 1 :=
    left_diagonal_difference_involution
  have hodd := higherOddCharge_odd (R := ℝ)
  rw [operatorParity_apply] at hodd
  have hright := congrArg (fun T : ZornOp ℝ => T * leftGrading) hodd
  have hswap : leftGrading * higherOddCharge (R := ℝ) =
      -(higherOddCharge * leftGrading) := by
    simpa only [mul_assoc, hΓ, mul_one, neg_mul] using hright
  apply trace_mul_square_eq_zero_of_anticommute
  rw [hswap, neg_add_cancel]

/-- Vanishing supertrace coexists with a nonzero, noncentral square and nonzero
graded-adjoint curvature on the entire operator algebra. -/
theorem higherOddCharge_supertrace_zero_with_nonzero_curvature :
    LinearMap.trace ℝ (ZornVectorMatrix ℝ)
        (leftGrading * (higherOddCharge * higherOddCharge)) = 0 ∧
      higherOddCharge (R := ℝ) * higherOddCharge ≠ 0 ∧
      (¬ ∀ T : ZornOp ℝ,
        Commute (higherOddCharge (R := ℝ) * higherOddCharge) T) ∧
      chargeDifferential (R := ℝ) * chargeDifferential ≠ 0 := by
  refine ⟨higherOddCharge_supertrace_zero, ?_, higherOddCharge_square_not_central,
    chargeDifferential_square_ne_zero⟩
  intro hzero
  apply higherOddCharge_square_not_central
  intro T
  rw [hzero]
  change (0 : ZornOp ℝ) * T = T * 0
  simp only [zero_mul, mul_zero]

end InfoGeometry.OperatorAlgebra.ZornMajoranaSupertrace

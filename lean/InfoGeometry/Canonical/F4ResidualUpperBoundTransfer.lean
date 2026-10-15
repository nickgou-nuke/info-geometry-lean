import Mathlib
import InfoGeometry.Canonical.F4LeibnizConstraintSpaceBridge
import InfoGeometry.Canonical.H3ZornCoordinateBasisBridge

/-!
Conditional dimension transfer for the native split-Albert derivation carrier.

This module identifies the kernel of the actual pointwise Jordan-Leibniz
residual with the derivation subspace. A lower bound of 677 on the residual
rank then gives the upper bound 52 on the derivation dimension. The rank bound
itself is deliberately not asserted here. To establish it by a finite
coordinate calculation, a separate readout theorem must first identify the
rank of this function-valued map with the rank of its finite residual tensor.
-/

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace InfoGeometry.Canonical.F4ResidualUpperBoundTransfer

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.F4LeibnizResidualBridge
open InfoGeometry.Canonical.H3ZornBasis

abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3
abbrev ResidualCarrier := H3 → H3 → H3

local instance : FiniteDimensional ℝ H3 :=
  h3ZornCoordinateBasis.finiteDimensional_of_finite

/-- The actual Jordan-Leibniz defect, as a linear map in its endomorphism
argument. -/
def residualLinear : EndH3 →ₗ[ℝ] ResidualCarrier where
  toFun D := F4LeibnizResidualBridge.residual D
  map_add' D E := by
    funext X Y
    change F4LeibnizResidualBridge.residual (D + E) X Y =
      F4LeibnizResidualBridge.residual D X Y +
        F4LeibnizResidualBridge.residual E X Y
    simp only [F4LeibnizResidualBridge.residual, LinearMap.add_apply]
    rw [← candidateJordanMul_eq_mul, ← candidateJordanMul_eq_mul,
      ← candidateJordanMul_eq_mul, candidateJordanMul_add_left,
      candidateJordanMul_add_right]
    simp only [candidateJordanMul_eq_mul]
    abel_nf
  map_smul' r D := by
    funext X Y
    change F4LeibnizResidualBridge.residual (r • D) X Y =
      r • F4LeibnizResidualBridge.residual D X Y
    simp only [F4LeibnizResidualBridge.residual, LinearMap.smul_apply]
    rw [← candidateJordanMul_eq_mul, ← candidateJordanMul_eq_mul,
      ← candidateJordanMul_eq_mul, candidateJordanMul_smul_left,
      candidateJordanMul_smul_right, smul_sub, smul_sub]
    simp only [candidateJordanMul_eq_mul]

/-- The kernel of the residual map is exactly the native Jordan derivation
subspace. -/
theorem residualLinear_ker_eq_derivations :
    LinearMap.ker residualLinear = H3ZornF4Derivations.toSubmodule := by
  ext D
  change residualLinear D = 0 ↔ H3ZornJordanDerivation D
  constructor
  · intro h
    apply (residual_zero_iff D).mp
    intro X Y
    have h' := congrFun (congrFun h X) Y
    exact h'
  · intro hD
    funext X Y
    exact (residual_zero_iff D).mpr hD X Y

/-- If the actual pointwise Leibniz residual map has rank at least 677, then
the native derivation carrier has dimension at most 52. This theorem does not
assert the rank premise or a finite-coordinate realization of it. -/
theorem derivation_finrank_le_52_of_residual_rank_ge_677
    (hRank : 677 ≤ Module.finrank ℝ (LinearMap.range residualLinear)) :
    Module.finrank ℝ H3ZornF4Derivations.toSubmodule ≤ 52 := by
  have hEnd : Module.finrank ℝ EndH3 = 729 := by
    rw [Module.finrank_linearMap, finrank_H3Zorn]
  have hRankNullity := LinearMap.finrank_range_add_finrank_ker residualLinear
  have hsum :
      Module.finrank ℝ (LinearMap.ker residualLinear) +
          Module.finrank ℝ (LinearMap.range residualLinear) = 729 := by
    rw [Nat.add_comm]
    simpa [hEnd] using hRankNullity
  have hker : Module.finrank ℝ (LinearMap.ker residualLinear) ≤ 52 := by omega
  rw [← residualLinear_ker_eq_derivations]
  exact hker

end InfoGeometry.Canonical.F4ResidualUpperBoundTransfer

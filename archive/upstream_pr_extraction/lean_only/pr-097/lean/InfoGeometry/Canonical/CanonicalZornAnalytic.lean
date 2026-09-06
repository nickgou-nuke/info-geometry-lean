/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Canonical.CanonicalZornMultiplicationBilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

/- The analytic structures use the existing native additive and scalar
operations; only the norm/topology layer is transported from coordinates. -/
noncomputable instance : NormedAddCommGroup CZ :=
  { NormedAddCommGroup.induced CZ CartesianCoordinates
      cartesianZornLinearEquiv.symm.toAddMonoidHom
      cartesianZornLinearEquiv.symm.injective with
    toAddCommGroup := inferInstance }

noncomputable instance : NormedSpace ℝ CZ :=
  NormedSpace.induced ℝ CZ CartesianCoordinates
    cartesianZornLinearEquiv.symm.toLinearMap

noncomputable instance : FiniteDimensional ℝ CZ :=
  FiniteDimensional.of_injective
    cartesianZornLinearEquiv.symm.toLinearMap
    cartesianZornLinearEquiv.symm.injective

noncomputable def zMulAnalyticOperatorLinear :
    CZ →ₗ[ℝ] (CZ →L[ℝ] CZ) where
  toFun X := (zMulBilinear X).toContinuousLinearMap
  map_add' X Y := by
    apply ContinuousLinearMap.ext
    intro Z
    exact congrArg (fun L : CZ →ₗ[ℝ] CZ => L Z)
      (zMulBilinear.map_add X Y)
  map_smul' r X := by
    apply ContinuousLinearMap.ext
    intro Z
    exact congrArg (fun L : CZ →ₗ[ℝ] CZ => L Z)
      (zMulBilinear.map_smul r X)

noncomputable def zMulAnalyticOperator :
    CZ →L[ℝ] (CZ →L[ℝ] CZ) :=
  zMulAnalyticOperatorLinear.toContinuousLinearMap

@[simp] theorem zMulAnalyticOperator_apply (X Y : CZ) :
    zMulAnalyticOperator X Y = zMul X Y := by
  change (zMulBilinear X) Y = zMul X Y
  rfl

theorem isBoundedBilinearMap_zMul :
    IsBoundedBilinearMap ℝ (fun p : CZ × CZ => zMul p.1 p.2) := by
  simpa only [zMulAnalyticOperator_apply] using
    zMulAnalyticOperator.isBoundedBilinearMap

theorem norm_zMul_le :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : CZ,
      ‖zMul X Y‖ ≤ C * ‖X‖ * ‖Y‖ := by
  simpa only [Prod.mk.eta] using (isBoundedBilinearMap_zMul).bound

theorem continuous_zMul_from_bounded :
    Continuous (fun p : CZ × CZ => zMul p.1 p.2) := by
  exact isBoundedBilinearMap_zMul.continuous

theorem hasStrictFDerivAt_zMul (p : CZ × CZ) :
    HasStrictFDerivAt
      (fun q : CZ × CZ => zMul q.1 q.2)
      ((isBoundedBilinearMap_zMul).deriv p) p := by
  exact isBoundedBilinearMap_zMul.hasStrictFDerivAt p

end
end InfoGeometry.Canonical

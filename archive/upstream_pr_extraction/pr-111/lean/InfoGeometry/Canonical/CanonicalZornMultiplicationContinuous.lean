import InfoGeometry.Canonical.CanonicalZornMultiplicationBilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

noncomputable def zMulRightCLM (X : CZ) : CZ →L[ℝ] CZ :=
  (zMulBilinear X).toContinuousLinearMap

noncomputable def zMulOperatorLinear :
    CZ →ₗ[ℝ] (CZ →L[ℝ] CZ) where
  toFun := zMulRightCLM
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

noncomputable def zMulOperatorCLM :
    CZ →L[ℝ] (CZ →L[ℝ] CZ) :=
  zMulOperatorLinear.toContinuousLinearMap

@[simp] theorem zMulOperatorCLM_apply (X Y : CZ) :
    zMulOperatorCLM X Y = zMul X Y := by
  rfl

theorem continuous_zMul_operator_eval :
    Continuous (fun p : CZ × CZ => zMulOperatorCLM p.1 p.2) := by
  simpa [zMulOperatorCLM_apply] using continuous_zMul

end
end InfoGeometry.Canonical

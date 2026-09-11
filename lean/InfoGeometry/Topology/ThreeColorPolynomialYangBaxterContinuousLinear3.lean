import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ThreeColorPolynomialYangBaxterContinuousLinear

/-!
# Continuous-linear Yang--Baxter operators on the three-colour tensor space

The two adjacent transpositions are lifted from the exact function-level
owner to `ContinuousLinearMap`.  The Yang--Baxter relation is proved both
pointwise and as an equality of continuous-linear operators.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge

noncomputable section

def colourR12Linear : ColorTensor3 →ₗ[ℚ] ColorTensor3 where
  toFun := R12
  map_add' X Y := by
    funext c₁ c₂ c₃
    rfl
  map_smul' a X := by
    funext c₁ c₂ c₃
    rfl

def colourR23Linear : ColorTensor3 →ₗ[ℚ] ColorTensor3 where
  toFun := R23
  map_add' X Y := by
    funext c₁ c₂ c₃
    rfl
  map_smul' a X := by
    funext c₁ c₂ c₃
    rfl

noncomputable def colourR12ContinuousLinear :
    ColorTensor3 →L[ℚ] ColorTensor3 :=
  ContinuousLinearMap.mk colourR12Linear
    (by simpa [colourR12Linear, topologicalR12]
      using continuous_topologicalR12)

noncomputable def colourR23ContinuousLinear :
    ColorTensor3 →L[ℚ] ColorTensor3 :=
  ContinuousLinearMap.mk colourR23Linear
    (by simpa [colourR23Linear, topologicalR23]
      using continuous_topologicalR23)

@[simp] theorem colourR12ContinuousLinear_apply
    (T : ColorTensor3) :
    colourR12ContinuousLinear T = R12 T := rfl

@[simp] theorem colourR23ContinuousLinear_apply
    (T : ColorTensor3) :
    colourR23ContinuousLinear T = R23 T := rfl

theorem colourR12ContinuousLinear_yang_baxter_pointwise
    (T : ColorTensor3) :
    colourR12ContinuousLinear
      (colourR23ContinuousLinear
        (colourR12ContinuousLinear T)) =
      colourR23ContinuousLinear
        (colourR12ContinuousLinear
          (colourR23ContinuousLinear T)) := by
  exact R_swap_yang_baxter T

theorem colourR12ContinuousLinear_yang_baxter :
    (colourR12ContinuousLinear.comp
      (colourR23ContinuousLinear.comp colourR12ContinuousLinear)) =
      (colourR23ContinuousLinear.comp
        (colourR12ContinuousLinear.comp colourR23ContinuousLinear)) := by
  apply ContinuousLinearMap.ext
  intro T
  exact colourR12ContinuousLinear_yang_baxter_pointwise T

@[simp] theorem colourR12ContinuousLinear_quadratic
    (T : ColorTensor3) :
    colourR12ContinuousLinear
      (colourR12ContinuousLinear T) = T := by
  rfl

@[simp] theorem colourR23ContinuousLinear_quadratic
    (T : ColorTensor3) :
    colourR23ContinuousLinear
      (colourR23ContinuousLinear T) = T := by
  rfl

end
end InfoGeometry.Topology

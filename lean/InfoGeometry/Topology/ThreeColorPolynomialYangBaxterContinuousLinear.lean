import Mathlib
import InfoGeometry.Topology.ThreeColorPolynomialYangBaxterTopological

/-!
# Continuous-linear lift of the exact three-colour swap

The canonical matrix owner contains the exact polynomial certificate.  This
owner lifts the same permutation to a continuous `ℚ`-linear endomorphism of
the finite colour tensor space, keeping the matrix and topological layers
separate.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge

noncomputable section

def colourSwapLinear : ColorTensor2 →ₗ[ℚ] ColorTensor2 where
  toFun := R_swap
  map_add' X Y := by
    funext c₁ c₂
    rfl
  map_smul' a X := by
    funext c₁ c₂
    rfl

noncomputable def colourSwapContinuousLinear :
    ColorTensor2 →L[ℚ] ColorTensor2 :=
  ContinuousLinearMap.mk colourSwapLinear
    (by simpa [colourSwapLinear, topologicalRSwap]
      using continuous_topologicalRSwap)

@[simp] theorem colourSwapContinuousLinear_apply
    (T : ColorTensor2) :
    colourSwapContinuousLinear T = R_swap T := rfl

@[simp] theorem colourSwapContinuousLinear_square
    (T : ColorTensor2) :
    colourSwapContinuousLinear
        (colourSwapContinuousLinear T) = T := by
  exact R_swap_quadratic_relation T

theorem colourSwapContinuousLinear_polynomial_certificate :
    ∀ T : ColorTensor2,
      colourSwapContinuousLinear
          (colourSwapContinuousLinear T) - T = 0 := by
  intro T
  simp

end
end InfoGeometry.Topology

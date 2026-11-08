import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge
import InfoGeometry.Topology.ThreeColorPolynomialYangBaxterContinuousLinear

/-!
# Matrix/function intertwiner for the three-colour swap

The canonical permutation matrix acts on pair-indexed vectors.  The curried
colour tensor space is explicitly identified with those vectors, and the
matrix action is shown to agree with the continuous-linear swap operator.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge

noncomputable section

def colourTensorToPair :
    ColorTensor2 ≃ₗ[ℚ] (ColourPair → ℚ) where
  toFun T := fun p => T p.1 p.2
  invFun v := fun a b => v (a, b)
  left_inv T := by
    funext a b
    rfl
  right_inv v := by
    funext p
    rcases p with ⟨a, b⟩
    rfl
  map_add' T U := by
    rfl
  map_smul' c T := by
    rfl

theorem colourSwap_matrix_vector_intertwines
  (T : ColorTensor2) :
    colourTensorToPair (colourSwapLinear T) =
      Matrix.mulVec (colourSwapR (K := ℚ))
        (colourTensorToPair T) := by
  ext p
  rcases p with ⟨a, b⟩
  change T b a = _
  simp [colourTensorToPair, colourSwapR,
    Matrix.permMatrix_mulVec, pairSwap]

theorem colourSwap_matrix_continuousLinear_intertwines
  (T : ColorTensor2) :
    colourTensorToPair (colourSwapContinuousLinear T) =
      Matrix.mulVec (colourSwapR (K := ℚ))
        (colourTensorToPair T) := by
  exact colourSwap_matrix_vector_intertwines T

end
end InfoGeometry.Topology

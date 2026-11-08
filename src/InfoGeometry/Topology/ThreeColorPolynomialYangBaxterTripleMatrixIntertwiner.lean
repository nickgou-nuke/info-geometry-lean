import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge
import InfoGeometry.Topology.ThreeColorPolynomialYangBaxterContinuousLinear3

/-!
# Triple matrix/function intertwiner

This is the triple analogue of the pair-level matrix square.  Canonical
`colourR12` and `colourR23` matrices act on pair-indexed vectors; the
continuous-linear operators act on curried `ColorTensor3` functions.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge

noncomputable section

def colourTensor3ToTriple :
    ColorTensor3 ≃ₗ[ℚ] (ColourTriple → ℚ) where
  toFun T := fun p => T p.1 p.2.1 p.2.2
  invFun v := fun a b c => v (a, b, c)
  left_inv T := by
    funext a b c
    rfl
  right_inv v := by
    funext p
    rcases p with ⟨a, b, c⟩
    rfl
  map_add' T U := by
    rfl
  map_smul' a T := by
    rfl

theorem colourR12_matrix_vector_intertwines
    (T : ColorTensor3) :
    colourTensor3ToTriple (colourR12ContinuousLinear T) =
      Matrix.mulVec (colourR12 (K := ℚ))
        (colourTensor3ToTriple T) := by
  ext p
  rcases p with ⟨a, b, c⟩
  change T b a c = _
  simp [colourTensor3ToTriple, colourR12,
    Matrix.permMatrix_mulVec, tripleSwap12]

theorem colourR23_matrix_vector_intertwines
    (T : ColorTensor3) :
    colourTensor3ToTriple (colourR23ContinuousLinear T) =
      Matrix.mulVec (colourR23 (K := ℚ))
        (colourTensor3ToTriple T) := by
  ext p
  rcases p with ⟨a, b, c⟩
  change T a c b = _
  simp [colourTensor3ToTriple, colourR23,
    Matrix.permMatrix_mulVec, tripleSwap23]

theorem colourR12R23_matrix_vector_yang_baxter
    (T : ColorTensor3) :
    Matrix.mulVec
        (colourR12 (K := ℚ) * colourR23 (K := ℚ) *
          colourR12 (K := ℚ))
        (colourTensor3ToTriple T) =
      Matrix.mulVec
        (colourR23 (K := ℚ) * colourR12 (K := ℚ) *
          colourR23 (K := ℚ))
        (colourTensor3ToTriple T) := by
  calc
    Matrix.mulVec
        (colourR12 (K := ℚ) * colourR23 (K := ℚ) *
          colourR12 (K := ℚ))
        (colourTensor3ToTriple T) =
            Matrix.mulVec (colourR12 (K := ℚ) * colourR23 (K := ℚ))
        (Matrix.mulVec (colourR12 (K := ℚ))
          (colourTensor3ToTriple T)) := by
            simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = Matrix.mulVec (colourR12 (K := ℚ))
        (Matrix.mulVec (colourR23 (K := ℚ))
          (Matrix.mulVec (colourR12 (K := ℚ))
          (colourTensor3ToTriple T))) := by
            simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = colourTensor3ToTriple
        (colourR12ContinuousLinear
          (colourR23ContinuousLinear
            (colourR12ContinuousLinear T))) := by
            rw [← colourR12_matrix_vector_intertwines,
              ← colourR23_matrix_vector_intertwines,
              ← colourR12_matrix_vector_intertwines]
    _ = colourTensor3ToTriple
        (colourR23ContinuousLinear
          (colourR12ContinuousLinear
            (colourR23ContinuousLinear T))) := by
            exact congrArg colourTensor3ToTriple
              (colourR12ContinuousLinear_yang_baxter_pointwise T)
    _ = Matrix.mulVec (colourR23 (K := ℚ))
        (Matrix.mulVec (colourR12 (K := ℚ))
          (Matrix.mulVec (colourR23 (K := ℚ))
            (colourTensor3ToTriple T))) := by
            rw [colourR23_matrix_vector_intertwines,
              colourR12_matrix_vector_intertwines,
              colourR23_matrix_vector_intertwines]
    _ = Matrix.mulVec
        (colourR23 (K := ℚ) * colourR12 (K := ℚ) *
          colourR23 (K := ℚ))
        (colourTensor3ToTriple T) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end
end InfoGeometry.Topology

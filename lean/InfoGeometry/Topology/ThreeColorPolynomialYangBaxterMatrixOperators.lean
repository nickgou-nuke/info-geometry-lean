import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge

/-!
# Matrix operators for the three-colour Yang--Baxter action

The canonical permutation matrices act on the finite vector space
`ColourTriple → ℚ` through `Matrix.mulVecLin`.  This owner exposes that
action as native linear and continuous-linear maps.  It does not identify
the external braid action with any non-associative Zorn multiplication.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

noncomputable section

abbrev ColourTripleVector := ColourTriple → ℚ

def colourR12MatrixLinear : ColourTripleVector →ₗ[ℚ] ColourTripleVector :=
  Matrix.mulVecLin (colourR12 (K := ℚ))

def colourR23MatrixLinear : ColourTripleVector →ₗ[ℚ] ColourTripleVector :=
  Matrix.mulVecLin (colourR23 (K := ℚ))

@[simp] theorem colourR12MatrixLinear_apply (v : ColourTripleVector) :
    colourR12MatrixLinear v =
      Matrix.mulVec (colourR12 (K := ℚ)) v := by
  rfl

@[simp] theorem colourR23MatrixLinear_apply (v : ColourTripleVector) :
    colourR23MatrixLinear v =
      Matrix.mulVec (colourR23 (K := ℚ)) v := by
  rfl

theorem colourR12MatrixLinear_yang_baxter :
    (colourR12MatrixLinear.comp
      (colourR23MatrixLinear.comp colourR12MatrixLinear)) =
      (colourR23MatrixLinear.comp
        (colourR12MatrixLinear.comp colourR23MatrixLinear)) := by
  apply LinearMap.ext
  intro v
  change colourR12MatrixLinear
      (colourR23MatrixLinear (colourR12MatrixLinear v)) =
    colourR23MatrixLinear
      (colourR12MatrixLinear (colourR23MatrixLinear v))
  simp only [colourR12MatrixLinear, colourR23MatrixLinear,
    Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [colourR12_artin_relation]

private theorem colourR12_matrix_sq :
    colourR12 (K := ℚ) * colourR12 (K := ℚ) = 1 := by
  simp only [colourR12]
  rw [← Matrix.permMatrix_mul]
  have h : tripleSwap12.symm * tripleSwap12.symm = 1 := by
    have hs : tripleSwap12.symm = tripleSwap12 := by
      apply Equiv.ext
      intro p
      rcases p with ⟨a, b, c⟩
      rfl
    rw [hs]
    apply Equiv.ext
    intro p
    rcases p with ⟨a, b, c⟩
    rfl
  rw [h]
  simp

private theorem colourR23_matrix_sq :
    colourR23 (K := ℚ) * colourR23 (K := ℚ) = 1 := by
  simp only [colourR23]
  rw [← Matrix.permMatrix_mul]
  have h : tripleSwap23.symm * tripleSwap23.symm = 1 := by
    have hs : tripleSwap23.symm = tripleSwap23 := by
      apply Equiv.ext
      intro p
      rcases p with ⟨a, b, c⟩
      rfl
    rw [hs]
    apply Equiv.ext
    intro p
    rcases p with ⟨a, b, c⟩
    rfl
  rw [h]
  simp

@[simp] theorem colourR12MatrixLinear_quadratic
    (v : ColourTripleVector) :
    colourR12MatrixLinear (colourR12MatrixLinear v) = v := by
  simpa [colourR12MatrixLinear, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, colourR12_matrix_sq]

@[simp] theorem colourR23MatrixLinear_quadratic
    (v : ColourTripleVector) :
    colourR23MatrixLinear (colourR23MatrixLinear v) = v := by
  simpa [colourR23MatrixLinear, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, colourR23_matrix_sq]

noncomputable def colourR12MatrixContinuousLinear :
    ColourTripleVector →L[ℚ] ColourTripleVector :=
  ContinuousLinearMap.mk colourR12MatrixLinear (by fun_prop)

noncomputable def colourR23MatrixContinuousLinear :
    ColourTripleVector →L[ℚ] ColourTripleVector :=
  ContinuousLinearMap.mk colourR23MatrixLinear (by fun_prop)

@[simp] theorem colourR12MatrixContinuousLinear_apply
    (v : ColourTripleVector) :
    colourR12MatrixContinuousLinear v = colourR12MatrixLinear v := by
  rfl

@[simp] theorem colourR23MatrixContinuousLinear_apply
    (v : ColourTripleVector) :
    colourR23MatrixContinuousLinear v = colourR23MatrixLinear v := by
  rfl

theorem colourR12MatrixContinuousLinear_yang_baxter :
    (colourR12MatrixContinuousLinear.comp
      (colourR23MatrixContinuousLinear.comp
        colourR12MatrixContinuousLinear)) =
      (colourR23MatrixContinuousLinear.comp
        (colourR12MatrixContinuousLinear.comp
          colourR23MatrixContinuousLinear)) := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [ContinuousLinearMap.comp_apply,
    colourR12MatrixContinuousLinear_apply,
    colourR23MatrixContinuousLinear_apply] using
    congrArg (fun f : ColourTripleVector →ₗ[ℚ] ColourTripleVector => f v)
      colourR12MatrixLinear_yang_baxter

end
end InfoGeometry.Topology

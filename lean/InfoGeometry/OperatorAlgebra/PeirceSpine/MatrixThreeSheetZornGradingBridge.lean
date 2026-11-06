/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization

/-!
# Euler-grading connection between the three-sheet matrix and Zorn models

The associative `3 × 3` matrix model has three diagonal coordinates, while
`OpZornMatrix` has two. The map below therefore forgets the `(2,2)` diagonal
coordinate. It is surjective, and it intertwines the two Euler actions. This
is a grading-level connection, not an algebra homomorphism or an identification
of the two operator products.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge

open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetKKTRealization

variable {B : Type*} [Ring B] [StarRing B]

/-- Project a three-sheet matrix to the eight Zorn coordinates. The `(2,2)`
diagonal entry is the only omitted matrix coordinate. -/
def matrix3ToOpZorn (X : Matrix (Fin 3) (Fin 3) B) : OpZornMatrix B :=
  ⟨X 0 0, ⟨X 1 0, X 0 2, X 2 1⟩, ⟨X 0 1, X 1 2, X 2 0⟩, X 1 1⟩

/-- Choose the representative with zero `(2,2)` entry for a Zorn element. -/
def opZornToMatrix3 (X : OpZornMatrix B) : Matrix (Fin 3) (Fin 3) B :=
  !![X.a, X.w.x, X.v.y; X.v.x, X.b, X.w.y; X.w.z, X.v.z, 0]

/-- The chosen matrix representative projects back to its Zorn coordinates. -/
theorem matrix3ToOpZorn_opZornToMatrix3 (X : OpZornMatrix B) :
    matrix3ToOpZorn (opZornToMatrix3 X) = X := by
  ext <;> rfl

/-- The projection is surjective, with `opZornToMatrix3` as a section. -/
theorem matrix3ToOpZorn_surjective : Function.Surjective
    (matrix3ToOpZorn (B := B)) := by
  intro X
  exact ⟨opZornToMatrix3 X, matrix3ToOpZorn_opZornToMatrix3 X⟩

omit [StarRing B] in
/-- Exact product comparison on the two outer matrix units `E₀₁` and `E₁₀`.
Their associative matrix product is `E₀₀`, while the prescribed Zorn product
of their images is the negative lower Cartan unit. Thus this projection
preserves the five-grade bookkeeping but does not identify the two products. -/
theorem matrix3ToOpZorn_matrixUnit_product_coordinates :
    let e₀₁ : Matrix (Fin 3) (Fin 3) B := !![0, 1, 0; 0, 0, 0; 0, 0, 0]
    let e₁₀ : Matrix (Fin 3) (Fin 3) B := !![0, 0, 0; 1, 0, 0; 0, 0, 0]
    matrix3ToOpZorn (e₀₁ * e₁₀) = (⟨1, 0, 0, 0⟩ : OpZornMatrix B) ∧
    matrix3ToOpZorn e₀₁ * matrix3ToOpZorn e₁₀ =
      (⟨0, 0, 0, -1⟩ : OpZornMatrix B) := by
  dsimp
  constructor
  · ext <;> simp [matrix3ToOpZorn, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext <;>
      simp [matrix3ToOpZorn, OpVec3.dot, OpVec3.leftScale, OpVec3.rightScale,
        OpVec3.skewCross, OpVec3.naiveCross]

omit [StarRing B] in
/-- The grading projection is not multiplicative on every nontrivial
coefficient ring. This concrete matrix-unit witness records the exact defect
without imposing diagonal or commutativity assumptions on the coefficients. -/
theorem matrix3ToOpZorn_not_multiplicative [Nontrivial B] :
    ∃ X Y : Matrix (Fin 3) (Fin 3) B,
      matrix3ToOpZorn (X * Y) ≠ matrix3ToOpZorn X * matrix3ToOpZorn Y := by
  rcases matrix3ToOpZorn_matrixUnit_product_coordinates (B := B) with ⟨hXY, hZorn⟩
  refine ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0],
    !![0, 0, 0; 1, 0, 0; 0, 0, 0], ?_⟩
  rw [hXY, hZorn]
  intro h
  have ha := congrArg (fun Z : OpZornMatrix B => Z.a) h
  exact one_ne_zero ha

/-- The two Euler actions commute with the projection. This states precisely
how the five grades in the associative matrix model map to the five grades in
the canonical operator-valued Zorn model. -/
theorem matrix3ToOpZorn_euler_intertwining
    (X : Matrix (Fin 3) (Fin 3) B) :
    matrix3ToOpZorn (eulerFiveGrading3 X) =
      opEulerFiveGrading (matrix3ToOpZorn X) := by
  ext <;>
    simp [matrix3ToOpZorn, eulerFiveGrading3, grade3Matrix,
      opEulerFiveGrading, Fin.val_zero, Fin.val_one, Fin.val_two] <;>
    norm_num <;> noncomm_ring

/-- The three-sheet Peirce projections map component-by-component to the
canonical Zorn grades. The neutral projection retains the two Zorn Cartan
coordinates and forgets the independent `(2,2)` diagonal coordinate, exactly
as specified by `matrix3ToOpZorn`. This is a statement about the grading
projection, not about preservation of associative products. -/
theorem matrix3ToOpZorn_five_grade_components
    (X : Matrix (Fin 3) (Fin 3) B) :
    matrix3ToOpZorn (peirceGradePlus2 (Nplus3 (B := B)) X) =
        opGradePlus2 (X 0 1) ∧
    matrix3ToOpZorn (peirceGradePlus1 (Nplus3 (B := B)) X) =
        opGradePlus1 (X 0 2) (X 2 1) ∧
    matrix3ToOpZorn (peirceGradeZero (Nplus3 (B := B)) X) =
        opGradeZero (X 0 0) (X 1 1) ∧
    matrix3ToOpZorn (peirceGradeMinus1 (Nplus3 (B := B)) X) =
        opGradeMinus1 (X 1 2) (X 2 0) ∧
    matrix3ToOpZorn (peirceGradeMinus2 (Nplus3 (B := B)) X) =
        opGradeMinus2 (X 1 0) := by
  rcases five_grade_matrix_coordinates (B := B) X with
    ⟨h₂, h₁, h₀, hₘ₁, hₘ₂⟩
  rw [h₂, h₁, h₀, hₘ₁, hₘ₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext <;>
    simp [matrix3ToOpZorn, opGradePlus2, opGradePlus1, opGradeZero, opCartanDiag,
      opGradeMinus1, opGradeMinus2]

/-- The top positive-grade matrix bracket vanishes and agrees with the
operator-Zorn commutator on the corresponding positive grades. -/
theorem matrix3ToOpZorn_plus2_plus1_bracket_compat
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    matrix3ToOpZorn
        (comm (peirceGradePlus2 (Nplus3 (B := B)) X)
          (peirceGradePlus1 (Nplus3 (B := B)) Y)) =
      opCommutator (opGradePlus2 (X 0 1))
        (opGradePlus1 (Y 0 2) (Y 2 1)) := by
  have hclosed := comm_peirceGradePlus2_plus1 (Nplus3 (B := B)) X Y
    (Nplus3_sq_zero (B := B)) (Nplus3_regular (B := B))
  rw [hclosed]
  ext <;>
    simp [matrix3ToOpZorn, opCommutator, opGradePlus1, opGradePlus2,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross] <;> noncomm_ring

/-- The bottom negative-grade matrix bracket vanishes and agrees with the
operator-Zorn commutator on the corresponding negative grades. -/
theorem matrix3ToOpZorn_minus2_minus1_bracket_compat
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    matrix3ToOpZorn
        (comm (peirceGradeMinus2 (Nplus3 (B := B)) X)
          (peirceGradeMinus1 (Nplus3 (B := B)) Y)) =
      opCommutator (opGradeMinus2 (X 1 0))
        (opGradeMinus1 (Y 1 2) (Y 2 0)) := by
  have hclosed := comm_peirceGradeMinus2_minus1 (Nplus3 (B := B)) X Y
    (Nplus3_sq_zero (B := B)) (Nplus3_regular (B := B))
  rw [hclosed]
  ext <;>
    simp [matrix3ToOpZorn, opCommutator, opGradeMinus1, opGradeMinus2,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross] <;> noncomm_ring

/-- The projection preserves commutators on the neutral diagonal sector:
the discarded `(2,2)` coordinate cannot affect the two retained Cartan
coordinates. This is unconditional over the coefficient ring. -/
theorem matrix3ToOpZorn_zero_zero_bracket_compat
    (X Y : Matrix (Fin 3) (Fin 3) B) :
    matrix3ToOpZorn
        (comm (peirceGradeZero (Nplus3 (B := B)) X)
          (peirceGradeZero (Nplus3 (B := B)) Y)) =
      opCommutator (opGradeZero (X 0 0) (X 1 1))
        (opGradeZero (Y 0 0) (Y 1 1)) := by
  rcases five_grade_matrix_coordinates (B := B) X with
    ⟨_, _, hX, _, _⟩
  rcases five_grade_matrix_coordinates (B := B) Y with
    ⟨_, _, hY, _, _⟩
  rw [hX, hY]
  ext <;>
    simp [matrix3ToOpZorn, comm, opCommutator, opGradeZero, opCartanDiag,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross]

/-- On the scalar-diagonal neutral slice, the matrix action on grade `+1`
matches the operator-Zorn commutator, even when the common diagonal value is
noncentral. -/
theorem matrix3ToOpZorn_zero_plus1_bracket_compat_of_scalar_diagonal
    (X Y : Matrix (Fin 3) (Fin 3) B)
    (h01 : X 0 0 = X 1 1) (h12 : X 1 1 = X 2 2) :
    matrix3ToOpZorn
        (comm (peirceGradeZero (Nplus3 (B := B)) X)
          (peirceGradePlus1 (Nplus3 (B := B)) Y)) =
      opCommutator (opGradeZero (X 0 0) (X 1 1))
        (opGradePlus1 (Y 0 2) (Y 2 1)) := by
  rw [zero_plus1_bracket_matrix_coordinates]
  ext <;>
    simp [matrix3ToOpZorn, opCommutator, opGradeZero, opCartanDiag,
      opGradePlus1, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      h01, h12]

/-- On the balanced neutral slice `X₀₀ = X₁₁`, the matrix-model
`[G₀,G₊₂]` bracket is carried to the operator-Zorn commutator. The equality
condition is explicit: without it, the two products act from opposite
diagonal entries and the projection is not asserted to preserve brackets. -/
theorem matrix3ToOpZorn_zero_plus2_bracket_compat_of_diagonal_eq
    (X Y : Matrix (Fin 3) (Fin 3) B) (hdiag : X 0 0 = X 1 1) :
    matrix3ToOpZorn
        (comm (peirceGradeZero (Nplus3 (B := B)) X)
          (peirceGradePlus2 (Nplus3 (B := B)) Y)) =
      opCommutator (opGradeZero (X 0 0) (X 1 1))
        (opGradePlus2 (Y 0 1)) := by
  rw [zero_plus2_bracket_matrix_coordinates]
  ext <;>
    simp [matrix3ToOpZorn, opCommutator, opGradeZero, opCartanDiag,
      opGradePlus2, OpVec3.leftScale, OpVec3.rightScale,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, hdiag]

/-- The matching balanced-slice compatibility for the negative extremal ray:
the matrix-model `[G₀,G₋₂]` bracket maps to the operator-Zorn commutator
when the two relevant neutral diagonal entries agree. -/
theorem matrix3ToOpZorn_zero_minus2_bracket_compat_of_diagonal_eq
    (X Y : Matrix (Fin 3) (Fin 3) B) (hdiag : X 0 0 = X 1 1) :
    matrix3ToOpZorn
        (comm (peirceGradeZero (Nplus3 (B := B)) X)
          (peirceGradeMinus2 (Nplus3 (B := B)) Y)) =
      opCommutator (opGradeZero (X 0 0) (X 1 1))
        (opGradeMinus2 (Y 1 0)) := by
  rw [zero_minus2_bracket_matrix_coordinates]
  ext <;>
    simp [matrix3ToOpZorn, opCommutator, opGradeZero, opCartanDiag,
      opGradeMinus2, OpVec3.leftScale, OpVec3.rightScale,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross, hdiag]

/-- The matrix Euler action factors through the Zorn model and the chosen
section. In particular, it kills the omitted `(2,2)` degree-zero coordinate. -/
theorem eulerFiveGrading3_factors_through_Zorn
    (X : Matrix (Fin 3) (Fin 3) B) :
    eulerFiveGrading3 X =
      opZornToMatrix3 (opEulerFiveGrading (matrix3ToOpZorn X)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix3ToOpZorn, opZornToMatrix3, eulerFiveGrading3,
      grade3Matrix, opEulerFiveGrading, Fin.val_zero, Fin.val_one,
      Fin.val_two] <;> norm_num <;> noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceSpine.MatrixThreeSheetZornGradingBridge

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinBottleTwistedRepresentationBridge

/-!
# A concrete matrix representation of the algebraic Klein group

This owner instantiates the existing presentation consumer on the standard
integral two-dimensional carrier.  The glide is the reflection
`diag (1, -1)` and the translation is the unit shear.  It proves the native
relation `G * T * G⁻¹ = T⁻¹` and packages the resulting homomorphism.

Only the finite matrix/group representation is claimed here: no topological
fundamental-group identification, C*-completion, or Tomita representation is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinBottleMatrixRepresentationBridge

open InfoGeometry.Canonical.KleinPresentedGroup

abbrev GL2Z := (Matrix (Fin 2) (Fin 2) ℤ)ˣ

def glideMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

def translationMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

def translationInverseMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]

abbrev Carrier2Z := InfoGeometry.Algebra.FiniteSpin.Vec2Z

def glideOperator : Carrier2Z →ₗ[ℤ] Carrier2Z :=
  Matrix.mulVecLin glideMatrix

def translationOperator : Carrier2Z →ₗ[ℤ] Carrier2Z :=
  Matrix.mulVecLin translationMatrix

def translationInverseOperator : Carrier2Z →ₗ[ℤ] Carrier2Z :=
  Matrix.mulVecLin translationInverseMatrix

theorem glideMatrix_sq : glideMatrix * glideMatrix = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glideMatrix, Matrix.mul_apply]

theorem translationMatrix_mul_inverse :
    translationMatrix * translationInverseMatrix =
      (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translationMatrix, translationInverseMatrix, Matrix.mul_apply]

theorem translationInverse_mul_matrix :
    translationInverseMatrix * translationMatrix =
      (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translationMatrix, translationInverseMatrix, Matrix.mul_apply]

def glideUnit : GL2Z :=
  { val := glideMatrix
    inv := glideMatrix
    val_inv := glideMatrix_sq
    inv_val := glideMatrix_sq }

def translationUnit : GL2Z :=
  { val := translationMatrix
    inv := translationInverseMatrix
    val_inv := translationMatrix_mul_inverse
    inv_val := translationInverse_mul_matrix }

theorem glideMatrix_conjugates_translationMatrix :
    glideMatrix * translationMatrix * glideMatrix = translationInverseMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glideMatrix, translationMatrix, translationInverseMatrix,
      Matrix.mul_apply]

theorem glideMatrix_mul_translationMatrix_eq_inverse_mul_glideMatrix :
    glideMatrix * translationMatrix =
      translationInverseMatrix * glideMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glideMatrix, translationMatrix, translationInverseMatrix,
      Matrix.mul_apply]

/- The same Klein relation on the concrete vector carrier `Fin 2 → ℤ`. -/
theorem glideOperator_conjugates_translationOperator (x : Fin 2 → ℤ) :
    Matrix.mulVec glideMatrix (Matrix.mulVec translationMatrix x) =
      Matrix.mulVec translationInverseMatrix (Matrix.mulVec glideMatrix x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    glideMatrix_mul_translationMatrix_eq_inverse_mul_glideMatrix]

theorem glideOperator_comp_translationOperator :
    glideOperator.comp translationOperator =
      translationInverseOperator.comp glideOperator := by
  apply LinearMap.ext
  intro x
  exact glideOperator_conjugates_translationOperator x

abbrev End2Z := (Carrier2Z →ₗ[ℤ] Carrier2Z)ˣ

theorem glideOperator_sq : glideOperator * glideOperator = 1 := by
  apply LinearMap.ext
  intro x
  change Matrix.mulVec glideMatrix (Matrix.mulVec glideMatrix x) = x
  rw [Matrix.mulVec_mulVec, glideMatrix_sq]
  simp

theorem translationOperator_mul_inverse :
    translationOperator * translationInverseOperator = 1 := by
  apply LinearMap.ext
  intro x
  change Matrix.mulVec translationMatrix
      (Matrix.mulVec translationInverseMatrix x) = x
  rw [Matrix.mulVec_mulVec, translationMatrix_mul_inverse]
  simp

theorem translationInverse_mul_operator :
    translationInverseOperator * translationOperator = 1 := by
  apply LinearMap.ext
  intro x
  change Matrix.mulVec translationInverseMatrix
      (Matrix.mulVec translationMatrix x) = x
  rw [Matrix.mulVec_mulVec, translationInverse_mul_matrix]
  simp

def glideOperatorUnit : End2Z :=
  { val := glideOperator
    inv := glideOperator
    val_inv := glideOperator_sq
    inv_val := glideOperator_sq }

def translationOperatorUnit : End2Z :=
  { val := translationOperator
    inv := translationInverseOperator
    val_inv := translationOperator_mul_inverse
    inv_val := translationInverse_mul_operator }

theorem glideOperatorUnit_conjugates_translationOperatorUnit :
    glideOperatorUnit * translationOperatorUnit * glideOperatorUnit⁻¹ =
      translationOperatorUnit⁻¹ := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  change Matrix.mulVec glideMatrix
      (Matrix.mulVec translationMatrix (Matrix.mulVec glideMatrix x)) =
    Matrix.mulVec translationInverseMatrix x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    glideMatrix_conjugates_translationMatrix]

def kleinOperatorRep : KleinGroup →* End2Z :=
  kleinRep glideOperatorUnit translationOperatorUnit
    glideOperatorUnit_conjugates_translationOperatorUnit

theorem kleinOperatorRep_generators :
    kleinOperatorRep (toKlein genA) = glideOperatorUnit ∧
    kleinOperatorRep (toKlein genB) = translationOperatorUnit := by
  exact kleinRep_relator_relation glideOperatorUnit translationOperatorUnit
    glideOperatorUnit_conjugates_translationOperatorUnit

theorem glideUnit_conjugates_translationUnit :
    glideUnit * translationUnit * glideUnit⁻¹ = translationUnit⁻¹ := by
  apply Units.ext
  exact glideMatrix_conjugates_translationMatrix

/-- The concrete integral matrix representation of the presented Klein group. -/
def kleinMatrixRep : KleinGroup →* GL2Z :=
  kleinRep glideUnit translationUnit glideUnit_conjugates_translationUnit

theorem kleinMatrixRep_generators :
    kleinMatrixRep (toKlein genA) = glideUnit ∧
    kleinMatrixRep (toKlein genB) = translationUnit := by
  exact kleinRep_relator_relation glideUnit translationUnit
    glideUnit_conjugates_translationUnit

theorem kleinMatrixRep_relation :
    kleinMatrixRep (toKlein genA) * kleinMatrixRep (toKlein genB) *
        (kleinMatrixRep (toKlein genA))⁻¹ =
      (kleinMatrixRep (toKlein genB))⁻¹ := by
  have hg := kleinMatrixRep_generators
  rw [hg.1, hg.2]
  exact glideUnit_conjugates_translationUnit

end InfoGeometry.Canonical.KleinBottleMatrixRepresentationBridge

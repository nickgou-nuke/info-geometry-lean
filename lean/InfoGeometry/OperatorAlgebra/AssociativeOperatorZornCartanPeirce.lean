import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-! The associative operator-Zorn shell is an ordinary transported `2 × 2`
matrix algebra.  This owner records only finite Peirce data independent of
the non-associative Zorn multiplication. -/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix

variable {A : Type*} [Ring A] [StarRing A]

abbrev ZornBlock (A : Type*) [Ring A] [StarRing A] := OperatorZornMatrix A

@[ext] theorem zornBlock_ext {X Y : ZornBlock A}
    (h₁ : X.n_plus_op = Y.n_plus_op)
    (h₂ : X.n_minus_op = Y.n_minus_op)
    (h₃ : X.sigma_plus_op = Y.sigma_plus_op)
    (h₄ : X.sigma_minus_op = Y.sigma_minus_op) : X = Y := by
  cases X
  cases Y
  simp_all

def ePlus : ZornBlock A := ⟨1, 0, 0, 0⟩
def eMinus : ZornBlock A := ⟨0, 1, 0, 0⟩
def grading : ZornBlock A := ⟨1, -1, 0, 0⟩
def sheetExchange : ZornBlock A := ⟨0, 0, 1, 1⟩

@[simp] theorem mul_n_plus_op (X Y : ZornBlock A) :
    (X * Y).n_plus_op =
      X.n_plus_op * Y.n_plus_op + X.sigma_plus_op * Y.sigma_minus_op := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0)
    (toMatrix_mul X Y)
  simpa [toMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h

@[simp] theorem mul_sigma_plus_op (X Y : ZornBlock A) :
    (X * Y).sigma_plus_op =
      X.n_plus_op * Y.sigma_plus_op + X.sigma_plus_op * Y.n_minus_op := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1)
    (toMatrix_mul X Y)
  simpa [toMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h

@[simp] theorem mul_sigma_minus_op (X Y : ZornBlock A) :
    (X * Y).sigma_minus_op =
      X.sigma_minus_op * Y.n_plus_op + X.n_minus_op * Y.sigma_minus_op := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 1 0)
    (toMatrix_mul X Y)
  simpa [toMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h

@[simp] theorem mul_n_minus_op (X Y : ZornBlock A) :
    (X * Y).n_minus_op =
      X.sigma_minus_op * Y.sigma_plus_op + X.n_minus_op * Y.n_minus_op := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 1 1)
    (toMatrix_mul X Y)
  simpa [toMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h

theorem ePlus_sq : ePlus * ePlus = (ePlus : ZornBlock A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (ePlus * ePlus) = toMatrix (ePlus : ZornBlock A)
  rw [toMatrix_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem eMinus_sq : eMinus * eMinus = (eMinus : ZornBlock A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (eMinus * eMinus) = toMatrix (eMinus : ZornBlock A)
  rw [toMatrix_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eMinus, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem ePlus_mul_eMinus : ePlus * eMinus = (0 : ZornBlock A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (ePlus * eMinus) = toMatrix (0 : ZornBlock A)
  rw [toMatrix_mul, toMatrix_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, eMinus, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem eMinus_mul_ePlus : eMinus * ePlus = (0 : ZornBlock A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (eMinus * ePlus) = toMatrix (0 : ZornBlock A)
  rw [toMatrix_mul, toMatrix_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, eMinus, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem ePlus_add_eMinus : ePlus + eMinus = (1 : ZornBlock A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (ePlus + eMinus) = toMatrix (1 : ZornBlock A)
  rw [toMatrix_add, toMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, eMinus, toMatrix]

theorem grading_sq : grading * grading = (1 : ZornBlock A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (grading * grading) = toMatrix (1 : ZornBlock A)
  rw [toMatrix_mul, toMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [grading, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def cartanInvolution (X : ZornBlock A) : ZornBlock A :=
  grading * X * grading

theorem cartanInvolution_involutive (X : ZornBlock A) :
    cartanInvolution (cartanInvolution X) = X := by
  unfold cartanInvolution
  calc
    grading * (grading * X * grading) * grading =
        (grading * grading) * X * (grading * grading) := by
      noncomm_ring
    _ = X := by simp [grading_sq]

theorem sheetExchange_sq : sheetExchange * sheetExchange = (1 : ZornBlock A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (sheetExchange * sheetExchange) = toMatrix (1 : ZornBlock A)
  rw [toMatrix_mul, toMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetExchange, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def cornerPP (X : ZornBlock A) : ZornBlock A := ePlus * X * ePlus
def cornerPM (X : ZornBlock A) : ZornBlock A := ePlus * X * eMinus
def cornerMP (X : ZornBlock A) : ZornBlock A := eMinus * X * ePlus
def cornerMM (X : ZornBlock A) : ZornBlock A := eMinus * X * eMinus

theorem four_corner_decomposition (X : ZornBlock A) :
    cornerPP X + cornerPM X + cornerMP X + cornerMM X = X := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (cornerPP X + cornerPM X + cornerMP X + cornerMM X) =
    toMatrix X
  rw [toMatrix_add, toMatrix_add, toMatrix_add]
  simp only [cornerPP, cornerPM, cornerMP, cornerMM]
  rw [toMatrix_mul, toMatrix_mul, toMatrix_mul, toMatrix_mul,
    toMatrix_mul, toMatrix_mul, toMatrix_mul, toMatrix_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ePlus, eMinus, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetExchange_conjugates (X : ZornBlock A) :
    sheetExchange * X * sheetExchange =
      ⟨X.n_minus_op, X.n_plus_op, X.sigma_minus_op, X.sigma_plus_op⟩ := by
  apply zornBlock_ext <;> simp [sheetExchange]

end InfoGeometry.OperatorAlgebra.AssociativeOperatorZornCartanPeirce

end

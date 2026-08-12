import InfoGeometry.Physics.ConnesDiracOperatorFromBdG
import Mathlib
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The operator carrier as a transported `2 × 2` matrix algebra

`OperatorZornMatrix` is a four-entry presentation of an ordinary chiral
block matrix.  All ring operations below are transported from Mathlib's
matrix operations; no separate Zorn multiplication is asserted here.
-/

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

namespace OperatorZornMatrix

abbrev Mat2 (A : Type*) := Matrix (Fin 2) (Fin 2) A

def toMatrix (M : OperatorZornMatrix A) : Mat2 A :=
  !![M.n_plus_op, M.sigma_plus_op; M.sigma_minus_op, M.n_minus_op]

def ofMatrix (M : Mat2 A) : OperatorZornMatrix A where
  n_plus_op := M 0 0
  n_minus_op := M 1 1
  sigma_plus_op := M 0 1
  sigma_minus_op := M 1 0

def equivMatrix : OperatorZornMatrix A ≃ Mat2 A where
  toFun := toMatrix
  invFun := ofMatrix
  left_inv := by
    intro M
    cases M
    rfl
  right_inv := by
    intro M
    funext i j
    fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem equivMatrix_apply (M : OperatorZornMatrix A) :
    equivMatrix M = toMatrix M := rfl

noncomputable instance : Ring (OperatorZornMatrix A) :=
  Equiv.ring (equivMatrix (A := A))

/-! ### Entrywise Nambu--Gorkov/Zorn multiplication

The product is the transported ordinary `2 × 2` matrix product.  These
lemmas expose its four operator-coordinate formulas without introducing a
second multiplication on the carrier.
-/

@[simp] theorem mul_n_plus_op (M N : OperatorZornMatrix A) :
    (M * N).n_plus_op =
      M.n_plus_op * N.n_plus_op + M.sigma_plus_op * N.sigma_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).n_plus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_sigma_plus_op (M N : OperatorZornMatrix A) :
    (M * N).sigma_plus_op =
      M.n_plus_op * N.sigma_plus_op + M.sigma_plus_op * N.n_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).sigma_plus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_sigma_minus_op (M N : OperatorZornMatrix A) :
    (M * N).sigma_minus_op =
      M.sigma_minus_op * N.n_plus_op + M.n_minus_op * N.sigma_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).sigma_minus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem mul_n_minus_op (M N : OperatorZornMatrix A) :
    (M * N).n_minus_op =
      M.sigma_minus_op * N.sigma_plus_op + M.n_minus_op * N.n_minus_op := by
  change (ofMatrix (toMatrix M * toMatrix N)).n_minus_op = _
  simp [ofMatrix, toMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The concrete Nambu--Gorkov square

The following is an identity in the transported matrix algebra.  It is kept
here, rather than in the non-associative canonical Zorn owner, because the
right-hand side uses the ordinary associative product on the four-entry
carrier.
-/

@[simp] theorem dirac_mul_dirac (Delta : A) :
    InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta =
      (⟨Delta * star Delta, star Delta * Delta, 0, 0⟩ :
        OperatorZornMatrix A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (_ * _) = toMatrix
    (⟨Delta * star Delta, star Delta * Delta, 0, 0⟩ :
      OperatorZornMatrix A)
  rw [Equiv.mul_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.diracOperator, toMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, equivMatrix, ofMatrix]

@[simp] theorem dirac_square_n_plus (Delta : A) :
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta).n_plus_op =
      Delta * star Delta := by
  simp [dirac_mul_dirac]

@[simp] theorem dirac_square_n_minus (Delta : A) :
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta).n_minus_op =
      star Delta * Delta := by
  simp [dirac_mul_dirac]

@[simp] theorem ofMatrix_toMatrix (M : OperatorZornMatrix A) :
    ofMatrix (toMatrix M) = M := (equivMatrix (A := A)).left_inv M

@[simp] theorem toMatrix_ofMatrix (M : Mat2 A) :
    toMatrix (ofMatrix M) = M := (equivMatrix (A := A)).right_inv M

@[simp] theorem equivMatrix_symm_apply (M : Mat2 A) :
    (equivMatrix (A := A)).symm M = ofMatrix M := rfl

def starOp (M : OperatorZornMatrix A) : OperatorZornMatrix A :=
  { n_plus_op := star M.n_plus_op
    n_minus_op := star M.n_minus_op
    sigma_plus_op := star M.sigma_minus_op
    sigma_minus_op := star M.sigma_plus_op }

instance : Star (OperatorZornMatrix A) := ⟨starOp⟩

@[simp] theorem star_eq_starOp (M : OperatorZornMatrix A) :
    star M = starOp M := rfl

@[simp] theorem toMatrix_starOp (M : OperatorZornMatrix A) :
    toMatrix (starOp M) = star (toMatrix M) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [starOp, toMatrix]

instance : StarRing (OperatorZornMatrix A) where
  star_involutive := by
    intro M
    apply (equivMatrix (A := A)).injective
    change toMatrix (starOp (starOp M)) = toMatrix M
    rw [toMatrix_starOp, toMatrix_starOp]
    exact star_star _
  star_mul := by
    intro M N
    apply (equivMatrix (A := A)).injective
    change toMatrix (starOp (M * N)) =
      toMatrix (starOp N * starOp M)
    simpa only [star_eq_starOp, equivMatrix_apply, toMatrix_starOp, Equiv.mul_def,
      equivMatrix_symm_apply, toMatrix_ofMatrix] using
      (Matrix.star_mul (toMatrix M) (toMatrix N))
  star_add := by
    intro M N
    apply (equivMatrix (A := A)).injective
    change toMatrix (starOp (M + N)) =
      toMatrix (starOp M + starOp N)
    simpa only [star_eq_starOp, equivMatrix_apply, toMatrix_starOp, Equiv.add_def,
      equivMatrix_symm_apply, toMatrix_ofMatrix] using
      (StarAddMonoid.star_add (toMatrix M) (toMatrix N))

@[simp] theorem starOp_starOp (M : OperatorZornMatrix A) :
    starOp (starOp M) = M := by
  apply (equivMatrix (A := A)).injective
  simp [starOp]

@[simp] theorem dirac_self_adjoint_native (Delta : A) :
    star (InfoGeometry.Physics.NCG.diracOperator Delta) =
      InfoGeometry.Physics.NCG.diracOperator Delta := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (starOp (InfoGeometry.Physics.NCG.diracOperator Delta)) =
    toMatrix (InfoGeometry.Physics.NCG.diracOperator Delta)
  rw [toMatrix_starOp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.diracOperator, toMatrix, Matrix.star_apply]

@[simp] theorem dirac_anticommutes_with_chirality_native (Delta : A) :
    InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.chiralGradingOperator +
      InfoGeometry.Physics.NCG.chiralGradingOperator *
        InfoGeometry.Physics.NCG.diracOperator Delta = 0 := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (_ + _) = toMatrix (0 : OperatorZornMatrix A)
  rw [Equiv.add_def, Equiv.mul_def, Equiv.mul_def, Equiv.zero_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.diracOperator,
      InfoGeometry.Physics.NCG.chiralGradingOperator, toMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, equivMatrix, ofMatrix]

@[simp] theorem chiral_grading_sq_native :
    InfoGeometry.Physics.NCG.chiralGradingOperator *
        InfoGeometry.Physics.NCG.chiralGradingOperator =
      (⟨1, 1, 0, 0⟩ : OperatorZornMatrix A) := by
  apply (equivMatrix (A := A)).injective
  change toMatrix (_ * _) = toMatrix (⟨1, 1, 0, 0⟩ : OperatorZornMatrix A)
  rw [Equiv.mul_def]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NCG.chiralGradingOperator, toMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, equivMatrix, ofMatrix]

end OperatorZornMatrix

end InfoGeometry.Physics

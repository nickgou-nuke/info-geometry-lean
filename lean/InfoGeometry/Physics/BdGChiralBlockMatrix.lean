import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Physics

/-!
The BdG/chiral block carrier is the ordinary matrix algebra
`Matrix (Fin 2) (Fin 2) A`.  It is not a Zorn algebra: the off-diagonal
entries are single elements of `A`, with no three-dimensional cross-product
or Zorn pairing.  The results below are purely matrix identities.
-/

abbrev BdGBlock (A : Type*) := Matrix (Fin 2) (Fin 2) A

variable {A : Type*} [Ring A] [StarRing A]

def chiralGrading : BdGBlock A :=
  !![1, 0; 0, -1]

def diracOperator (Delta : A) : BdGBlock A :=
  !![0, Delta; star Delta, 0]

/-! The square below is defined by the native matrix multiplication. -/

def diracSquare (Delta : A) : BdGBlock A :=
  diracOperator Delta * diracOperator Delta

@[simp] theorem diracSquare_eq_diagonal (Delta : A) :
    diracSquare Delta =
      !![Delta * star Delta, 0;
         0, star Delta * Delta] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracSquare, diracOperator, Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp] theorem diracSquare_offDiagonal_zero (Delta : A) :
    diracSquare Delta 0 1 = 0 ∧
      diracSquare Delta 1 0 = 0 := by
  rw [diracSquare_eq_diagonal]
  simp

@[simp] theorem diracSquare_diag_entries (Delta : A) :
    diracSquare Delta 0 0 = Delta * star Delta ∧
      diracSquare Delta 1 1 = star Delta * Delta := by
  rw [diracSquare_eq_diagonal]
  simp

theorem diracSquare_eq_one_of_twoSidedIsometry
    (Delta : A)
    (hLeft : Delta * star Delta = 1)
    (hRight : star Delta * Delta = 1) :
    diracSquare Delta = 1 := by
  rw [diracSquare_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hLeft, hRight]

/-!
`Matrix (Fin 2) (Fin 2) A` has Mathlib's native star instance, namely
conjugate transpose.  This alias preserves the earlier explicit name while
making the carrier's star structure the native one.
-/
abbrev bdgStar (M : BdGBlock A) : BdGBlock A := star M

@[simp] theorem bdgStar_apply (M : BdGBlock A) (i j : Fin 2) :
    bdgStar M i j = star (M j i) := by
  simp [bdgStar]

@[simp] theorem chiralGrading_sq :
    chiralGrading * chiralGrading = (1 : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem dirac_self_adjoint (Delta : A) :
    bdgStar (diracOperator Delta) = diracOperator Delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgStar, diracOperator]

@[simp] theorem dirac_anticommutes_with_chirality (Delta : A) :
    diracOperator Delta * chiralGrading +
        chiralGrading * diracOperator Delta = (0 : BdGBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracOperator, chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- Connes' commutator differential on the BdG block carrier. -/
def connesDifferential (D a : BdGBlock A) : BdGBlock A :=
  D * a - a * D

@[simp] theorem connesDifferential_one (D : BdGBlock A) :
    connesDifferential D 1 = 0 := by
  simp [connesDifferential]

theorem connesDifferential_add (D a b : BdGBlock A) :
    connesDifferential D (a + b) =
      connesDifferential D a + connesDifferential D b := by
  unfold connesDifferential
  noncomm_ring

@[simp] theorem connesDifferential_mul (D a b : BdGBlock A) :
    connesDifferential D (a * b) =
      connesDifferential D a * b + a * connesDifferential D b := by
  simp [connesDifferential]
  noncomm_ring

theorem star_connesDifferential (D a : BdGBlock A) :
    star (connesDifferential D a) =
      -connesDifferential (star D) (star a) := by
  simp [connesDifferential]

theorem star_connesDifferential_of_selfAdjoint
    {D : BdGBlock A} (hD : star D = D) (a : BdGBlock A) :
    star (connesDifferential D a) =
      -connesDifferential D (star a) := by
  rw [star_connesDifferential, hD]

/-! A compact property collecting the finite matrix identities above. -/
theorem bdg_chiral_block_matrix_synthesis (Delta : A) (D a b : BdGBlock A) :
    (chiralGrading * chiralGrading = (1 : BdGBlock A)) ∧
    (bdgStar (diracOperator Delta) = diracOperator Delta) ∧
    (diracOperator Delta * chiralGrading +
      chiralGrading * diracOperator Delta = (0 : BdGBlock A)) ∧
    (connesDifferential D (a * b) =
      connesDifferential D a * b + a * connesDifferential D b) :=
  ⟨chiralGrading_sq, dirac_self_adjoint Delta,
    dirac_anticommutes_with_chirality Delta, connesDifferential_mul D a b⟩

end InfoGeometry.Physics

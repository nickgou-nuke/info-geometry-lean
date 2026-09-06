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

theorem diracSquare_trace (Delta : A) :
    Matrix.trace (diracSquare Delta) =
      Delta * star Delta + star Delta * Delta := by
  rw [diracSquare_eq_diagonal]
  simp [Matrix.trace, Fin.sum_univ_two]

theorem diracSquare_trace_of_twoSidedIsometry
    (Delta : A)
    (hLeft : Delta * star Delta = 1)
    (hRight : star Delta * Delta = 1) :
    Matrix.trace (diracSquare Delta) = (1 : A) + 1 := by
  rw [diracSquare_trace, hLeft, hRight]

theorem diracSquare_eq_one_of_twoSidedIsometry
    (Delta : A)
    (hLeft : Delta * star Delta = 1)
    (hRight : star Delta * Delta = 1) :
    diracSquare Delta = 1 := by
  rw [diracSquare_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hLeft, hRight]

theorem diracSquare_eq_one_iff (Delta : A) :
    diracSquare Delta = (1 : BdGBlock A) ↔
      Delta * star Delta = 1 ∧ star Delta * Delta = 1 := by
  constructor
  · intro h
    have hLeft := congrArg (fun M : BdGBlock A => M 0 0) h
    have hRight := congrArg (fun M : BdGBlock A => M 1 1) h
    rw [diracSquare_eq_diagonal] at hLeft hRight
    exact ⟨by simpa using hLeft, by simpa using hRight⟩
  · rintro ⟨hLeft, hRight⟩
    exact diracSquare_eq_one_of_twoSidedIsometry Delta hLeft hRight

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

/-! These finite identities are the theorem-safe spectral shadow of the
particle-hole/chiral picture.  They do not assert an analytic spectrum. -/

theorem diracOperator_trace_zero (Delta : A) :
    Matrix.trace (diracOperator Delta) = 0 := by
  simp [diracOperator, Matrix.trace, Fin.sum_univ_two]

theorem chiral_conjugation_dirac_neg (Delta : A) :
    chiralGrading * diracOperator Delta * chiralGrading =
      -diracOperator Delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, diracOperator, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiral_conjugation_diracSquare (Delta : A) :
    chiralGrading * (diracOperator Delta * diracOperator Delta) *
        chiralGrading = diracOperator Delta * diracOperator Delta := by
  change chiralGrading * diracSquare Delta * chiralGrading = diracSquare Delta
  rw [diracSquare_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

theorem diracSquare_commutes_with_chirality (Delta : A) :
    diracSquare Delta * chiralGrading =
      chiralGrading * diracSquare Delta := by
  rw [diracSquare_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem diracSquare_self_adjoint (Delta : A) :
    bdgStar (diracSquare Delta) = diracSquare Delta := by
  rw [diracSquare_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgStar, Matrix.mul_apply, Fin.sum_univ_two]

/-- Connes' commutator differential on the BdG block carrier. -/
def connesDifferential (D a : BdGBlock A) : BdGBlock A :=
  D * a - a * D

@[simp] theorem connesDifferential_one (D : BdGBlock A) :
    connesDifferential D 1 = 0 := by
  simp [connesDifferential]

@[simp] theorem connesDifferential_zero (D : BdGBlock A) :
    connesDifferential D 0 = 0 := by
  simp [connesDifferential]

@[simp] theorem connesDifferential_self (D : BdGBlock A) :
    connesDifferential D D = 0 := by
  simp [connesDifferential]

theorem connesDifferential_eq_zero_iff (D a : BdGBlock A) :
    connesDifferential D a = 0 ↔ D * a = a * D := by
  simp [connesDifferential, sub_eq_zero]

theorem connesDifferential_add (D a b : BdGBlock A) :
    connesDifferential D (a + b) =
      connesDifferential D a + connesDifferential D b := by
  unfold connesDifferential
  noncomm_ring

theorem connesDifferential_sub (D a b : BdGBlock A) :
    connesDifferential D (a - b) =
      connesDifferential D a - connesDifferential D b := by
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

/-! The quadratic/trace readout is packaged separately so downstream users can
reuse it without unpacking the basic spectral-triple synthesis. -/
theorem bdg_chiral_block_matrix_quadratic_synthesis (Delta : A) :
    Matrix.trace (diracOperator Delta) = 0 ∧
    diracSquare Delta =
      !![Delta * star Delta, 0;
         0, star Delta * Delta] ∧
    Matrix.trace (diracSquare Delta) =
      Delta * star Delta + star Delta * Delta ∧
    chiralGrading * (diracSquare Delta) * chiralGrading = diracSquare Delta := by
  exact ⟨diracOperator_trace_zero Delta,
    diracSquare_eq_diagonal Delta,
    diracSquare_trace Delta,
    chiral_conjugation_diracSquare Delta⟩

end InfoGeometry.Physics

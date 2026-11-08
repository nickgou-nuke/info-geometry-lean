/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixNoncommutativity
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
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

variable {A : Type*} [Ring A]

def chiralGrading : BdGBlock A :=
  !![1, 0; 0, -1]

/-- The mass-coupled BdG block matrix over a possibly noncommutative ring.
Its entries are operators when `A` is an endomorphism ring. -/
def massiveBdGHamiltonian (D M : A) : BdGBlock A :=
  !![D, M; M, -D]

/-- Squaring the BdG block operator gives the common diagonal `D² + M²` when
the kinetic and pairing operators commute. The commutation hypothesis is
exactly what removes the two off-diagonal commutators. -/
theorem massiveBdGHamiltonian_sq (D M : A) (hcomm : D * M = M * D) :
    massiveBdGHamiltonian D M * massiveBdGHamiltonian D M =
      !![D * D + M * M, 0; 0, D * D + M * M] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massiveBdGHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
      hcomm, mul_neg, neg_mul, neg_neg] <;> abel

/-- The particle--hole swap on the two operator sectors. -/
def andreevSwap : BdGBlock A := !![0, 1; 1, 0]

@[simp] theorem andreevSwap_sq :
    andreevSwap (A := A) * andreevSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [andreevSwap, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation by the Andreev swap exchanges particle and hole blocks. -/
theorem andreevSwap_conj (X : BdGBlock A) :
    andreevSwap * X * andreevSwap = !![X 1 1, X 1 0; X 0 1, X 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [andreevSwap, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

/-- The massive BdG square has a precisely identified off-diagonal commutator
obstruction. This statement keeps both operator orders in the diagonal blocks. -/
theorem massiveBdGHamiltonian_sq_with_commutator (D M : A) :
    massiveBdGHamiltonian D M * massiveBdGHamiltonian D M =
      !![D * D + M * M, D * M - M * D;
         M * D - D * M, M * M + D * D] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massiveBdGHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
      mul_neg, neg_mul, neg_neg] <;> abel

/-- The swap-even part of the massive square, retaining the two ordered
operator products on its two sectors. -/
def massiveBdGSquareEven (D M : A) : BdGBlock A :=
  !![D * D + M * M, 0; 0, M * M + D * D]

/-- The swap-odd commutator anomaly in the massive BdG square. -/
def massiveBdGCommutatorAnomaly (D M : A) : BdGBlock A :=
  !![0, D * M - M * D; M * D - D * M, 0]

/-- The BdG interaction anomaly vanishes exactly when the kinetic and mass
operators commute. -/
theorem massiveBdGCommutatorAnomaly_eq_zero_iff_commute (D M : A) :
    massiveBdGCommutatorAnomaly D M = 0 ↔ D * M = M * D := by
  constructor
  · intro h
    have h01 := congrArg (fun X : BdGBlock A => X 0 1) h
    have hcomm : D * M - M * D = 0 := by
      simpa [massiveBdGCommutatorAnomaly] using h01
    exact sub_eq_zero.mp hcomm
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [massiveBdGCommutatorAnomaly, h]

/-- The full square is the sum of its ordered even part and its commutator
anomaly. -/
theorem massiveBdGHamiltonian_sq_split (D M : A) :
    massiveBdGHamiltonian D M * massiveBdGHamiltonian D M =
      massiveBdGSquareEven D M + massiveBdGCommutatorAnomaly D M := by
  rw [massiveBdGHamiltonian_sq_with_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massiveBdGSquareEven, massiveBdGCommutatorAnomaly,
      Matrix.add_apply, add_assoc]

/-- Andreev reflection changes the sign of the commutator anomaly. -/
theorem andreev_reflect_mass_commutator_anomaly (D M : A) :
    andreevSwap * massiveBdGCommutatorAnomaly D M * andreevSwap =
      -massiveBdGCommutatorAnomaly D M := by
  rw [andreevSwap_conj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massiveBdGCommutatorAnomaly, andreevSwap]

/-- Andreev-reflecting the square reverses the two off-diagonal commutator
terms. Adding particle and hole contributions cancels the anomaly without a
commutativity hypothesis; the diagonal operator orders remain explicit. -/
theorem massiveBdGHamiltonian_andreev_anomaly_cancellation (D M : A) :
    massiveBdGHamiltonian D M * massiveBdGHamiltonian D M +
      andreevSwap * (massiveBdGHamiltonian D M * massiveBdGHamiltonian D M) * andreevSwap =
        !![D * D + M * M + (M * M + D * D), 0;
           0, M * M + D * D + (D * D + M * M)] := by
  rw [massiveBdGHamiltonian_sq_with_commutator, andreevSwap_conj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> abel

/-- Exact criterion for Andreev invariance of the squared massive operator.
In an arbitrary coefficient ring, the criterion is that twice the ordered
commutator vanish; identifying this with commutation requires excluding
2-torsion. -/
theorem massiveBdGHamiltonian_square_andreev_invariant_iff_twice_commutator_eq_zero
    (D M : A) :
    andreevSwap * (massiveBdGHamiltonian D M * massiveBdGHamiltonian D M) * andreevSwap =
      massiveBdGHamiltonian D M * massiveBdGHamiltonian D M ↔
        (D * D + M * M = M * M + D * D) ∧
          (D * M - M * D) + (D * M - M * D) = 0 := by
  rw [massiveBdGHamiltonian_sq_with_commutator, andreevSwap_conj]
  constructor
  · intro h
    have h00 := congrArg (fun X : BdGBlock A => X 0 0) h
    have h01 := congrArg (fun X : BdGBlock A => X 0 1) h
    constructor
    · simpa using h00.symm
    · change M * D - D * M = D * M - M * D at h01
      nth_rewrite 2 [← h01]
      abel
  · intro h
    rcases h with ⟨hdiag, hcomm⟩
    have hcross : M * D - D * M = D * M - M * D := by
      calc
        M * D - D * M = -(D * M - M * D) := by noncomm_ring
        _ = D * M - M * D := (eq_neg_iff_add_eq_zero).2 hcomm |>.symm
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using hdiag.symm
    · simpa using hcross
    · simpa using hcross.symm
    · simpa using hdiag

/-- The operator-valued twelfth cyclotomic polynomial. This is a polynomial
in the full operator, with no diagonalization or spectral-coordinate choice. -/
def operatorCyclotomicHiggs (H : BdGBlock A) : BdGBlock A := H ^ 4 - H ^ 2 + 1

/-- Polynomial evaluation is covariant under the Andreev involution. -/
theorem andreev_operatorCyclotomicHiggs (H : BdGBlock A) :
    andreevSwap * operatorCyclotomicHiggs H * andreevSwap =
      operatorCyclotomicHiggs (andreevSwap * H * andreevSwap) := by
  have hS := andreevSwap_sq (A := A)
  have hmul (X Y : BdGBlock A) :
      andreevSwap * (X * Y) * andreevSwap =
        (andreevSwap * X * andreevSwap) * (andreevSwap * Y * andreevSwap) := by
    calc
      andreevSwap * (X * Y) * andreevSwap =
          andreevSwap * X * (1 : BdGBlock A) * Y * andreevSwap := by noncomm_ring
      _ = andreevSwap * X * (andreevSwap * andreevSwap) * Y * andreevSwap := by rw [hS]
      _ = (andreevSwap * X * andreevSwap) * (andreevSwap * Y * andreevSwap) := by noncomm_ring
  have hpow (n : ℕ) :
      andreevSwap * H ^ n * andreevSwap = (andreevSwap * H * andreevSwap) ^ n := by
    induction n with
    | zero => simp [hS]
    | succ n ih =>
        calc
          andreevSwap * H ^ (n + 1) * andreevSwap =
              andreevSwap * (H ^ n * H) * andreevSwap := by rw [pow_succ]
          _ = (andreevSwap * H ^ n * andreevSwap) *
                (andreevSwap * H * andreevSwap) := hmul _ _
          _ = (andreevSwap * H * andreevSwap) ^ (n + 1) := by
                rw [ih, pow_succ]
  unfold operatorCyclotomicHiggs
  calc
    andreevSwap * (H ^ 4 - H ^ 2 + 1) * andreevSwap =
        andreevSwap * H ^ 4 * andreevSwap - andreevSwap * H ^ 2 * andreevSwap +
          andreevSwap * 1 * andreevSwap := by noncomm_ring
    _ = (andreevSwap * H * andreevSwap) ^ 4 -
          (andreevSwap * H * andreevSwap) ^ 2 + 1 := by
      rw [hpow 4, hpow 2]
      simp [hS]

/-- For the massive operator, the cyclotomic Higgs polynomial transforms by
the same hole reflection that cancels the commutator anomaly in its square. -/
theorem massiveBdGHamiltonian_higgs_reflection (D M : A) :
    andreevSwap * operatorCyclotomicHiggs (massiveBdGHamiltonian D M) * andreevSwap =
      operatorCyclotomicHiggs
        (andreevSwap * massiveBdGHamiltonian D M * andreevSwap) :=
  andreev_operatorCyclotomicHiggs (massiveBdGHamiltonian D M)

/-! The square below is defined by the native matrix multiplication. -/

variable [StarRing A]

def diracOperator (Delta : A) : BdGBlock A :=
  !![0, Delta; star Delta, 0]

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

omit [StarRing A] in
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

/-- Conjugating the self-adjoint Dirac block by the chiral involution changes
its sign.  This is the concrete finite-dimensional Krein-adjoint identity. -/
theorem dirac_krein_adjoint (Delta : A) :
    chiralGrading * star (diracOperator Delta) * chiralGrading =
      -diracOperator Delta := by
  have hstar : star (diracOperator Delta) = diracOperator Delta := by
    simpa [bdgStar] using dirac_self_adjoint Delta
  rw [hstar]
  have hJ := chiralGrading_sq (A := A)
  have hanti := dirac_anticommutes_with_chirality Delta
  have hleft : chiralGrading * diracOperator Delta =
      -(diracOperator Delta * chiralGrading) := by
    have hanti' : chiralGrading * diracOperator Delta +
        diracOperator Delta * chiralGrading = 0 := by
      simpa [add_comm] using hanti
    exact (add_eq_zero_iff_eq_neg.mp hanti')
  calc
    chiralGrading * diracOperator Delta * chiralGrading =
        -(diracOperator Delta * chiralGrading * chiralGrading) := by
          rw [hleft]
          rw [neg_mul]
    _ = -diracOperator Delta := by rw [mul_assoc, hJ, mul_one]

/-! The off-diagonal Dirac block sends the first chiral sheet to the second. -/
theorem diracOperator_mulVec_inl (Delta : A) (x : A) :
    Matrix.mulVec (diracOperator Delta) ![x, 0] = ![0, star Delta * x] := by
  funext i
  fin_cases i <;>
    simp [diracOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! The off-diagonal Dirac block sends the second chiral sheet to the first. -/
theorem diracOperator_mulVec_inr (Delta : A) (y : A) :
    Matrix.mulVec (diracOperator Delta) ![0, y] = ![Delta * y, 0] := by
  funext i
  fin_cases i <;>
    simp [diracOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! A nonzero off-diagonal parameter produces a nonzero sheet-mixing action. -/
theorem diracOperator_mulVec_inr_ne_zero {Delta : A} (hDelta : Delta ≠ 0) :
    Matrix.mulVec (diracOperator Delta) ![0, 1] ≠ 0 := by
  rw [diracOperator_mulVec_inr]
  intro h
  apply hDelta
  simpa using congrFun h 0

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

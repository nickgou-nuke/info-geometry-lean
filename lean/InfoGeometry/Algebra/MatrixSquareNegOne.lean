/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.MatrixAmplification
import InfoGeometry.Algebra.HypercomplexTriadMatrix
import Mathlib.Algebra.Group.Semiconj.Units
import Mathlib.Algebra.Module.Opposite
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Square roots of minus one over matrix coefficient rings

The diagonal and conjugation constructions use an arbitrary associative unital
ring. Only the odd-cardinality determinant criterion assumes commutativity.
Right multiplication on coefficient columns commutes with the whole left matrix
action; a scalar matrix with a noncentral coefficient need not do so.

The explicit shear family supplies distinct roots and a fixed-metric
counterexample. Characteristic two is expressed by the minimal equation `2 = 0`.
No division-ring determinant, spectral classification, or Hilbert completion is
inferred from these ring calculations.
-/

namespace InfoGeometry.Algebra.MatrixSquareNegOne

variable {R : Type*} [Ring R]

/-- A negative-square element is a genuine ring unit, with inverse its negative. -/
theorem isUnit_of_square_eq_neg_one (x : R) (hx : x * x = -1) : IsUnit x := by
  refine ⟨⟨x, -x, ?_, ?_⟩, rfl⟩
  · rw [mul_neg, hx, neg_neg]
  · rw [neg_mul, hx, neg_neg]

/-- Native unit conjugation preserves and reflects the negative-square equation. -/
theorem unit_conjugate_square_eq_neg_one_iff (u : Rˣ) (x : R) :
    (↑u * x * ↑u⁻¹) * (↑u * x * ↑u⁻¹) = -(1 : R) ↔ x * x = -1 := by
  have transport (v : Rˣ) (y : R) (hy : y * y = -1) :
      (↑v * y * ↑v⁻¹) * (↑v * y * ↑v⁻¹) = -(1 : R) := by
    calc
      (↑v * y * ↑v⁻¹) * (↑v * y * ↑v⁻¹) = ↑v * (y * y) * ↑v⁻¹ := by
        simpa only [pow_two] using v.conj_pow y 2
      _ = -1 := by rw [hy]; simp
  constructor
  · intro h
    simpa [mul_assoc] using transport u⁻¹ (↑u * x * ↑u⁻¹) h
  · exact transport u x

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mixed diagonal roots need no pairwise commutativity assumption. -/
theorem diagonal_square_eq_neg_one_iff (d : n → R) :
    Matrix.diagonal d * Matrix.diagonal d = -1 ↔ ∀ i, d i * d i = -1 := by
  rw [Matrix.diagonal_mul_diagonal]
  constructor
  · intro h i
    have hi := congrArg (fun A : Matrix n n R => A i i) h
    simpa using hi
  · intro h
    have hd : (fun i => d i * d i) = fun _ => -(1 : R) := funext h
    rw [hd]
    simpa only [Matrix.diagonal_one] using
      (Matrix.diagonal_neg (fun _ : n => (1 : R))).symm

/-- The actual native scalar ring homomorphism amplifies a coefficient root. -/
theorem scalar_square_eq_neg_one (j : R) (hj : j * j = -1) :
    Matrix.scalar n j * Matrix.scalar n j = -1 := by
  simpa only [map_mul, map_neg, map_one] using congrArg (Matrix.scalar n) hj

/-- A nonempty scalar amplification also reflects the coefficient equation. -/
theorem scalar_square_eq_neg_one_iff [Nonempty n] (j : R) :
    Matrix.scalar n j * Matrix.scalar n j = -1 ↔ j * j = -1 := by
  rw [← map_mul, ← map_one (Matrix.scalar n), ← map_neg, Matrix.scalar_inj]

omit [DecidableEq n] in
/-- Right multiplication is compatible with every left matrix observable.
This is the native opposite-ring scalar action, not centrality of `j`. -/
theorem mulVec_commutes_right_phase (A : Matrix n n R) (j : R) :
    Function.Commute A.mulVec (fun v i => v i * j) := by
  intro v
  change A.mulVec ((MulOpposite.op j) • v) =
    (MulOpposite.op j) • A.mulVec v
  exact Matrix.mulVec_smul A (MulOpposite.op j) v

end Matrices

/-- The right action on coefficient columns has the required square law. -/
theorem right_phase_square {n : Type*} (j : R) (hj : j * j = -1) (v : n → R) :
    (fun i => (v i * j) * j) = -v := by
  funext i
  simp only [mul_assoc, hj, mul_neg_one, Pi.neg_apply]

section Commutative

variable {S : Type*} [CommRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Odd matrix size over a commutative ring detects exactly a coefficient root.
No field or characteristic-zero hypothesis is used. -/
theorem exists_matrix_square_eq_neg_one_iff_of_odd (hodd : Odd (Fintype.card n)) :
    (∃ A : Matrix n n S, A * A = -1) ↔ ∃ j : S, j * j = -1 := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A.det, ?_⟩
    calc
      A.det * A.det = (A * A).det := (Matrix.det_mul A A).symm
      _ = (-(1 : Matrix n n S)).det := congrArg Matrix.det hA
      _ = -1 := by rw [Matrix.det_neg, hodd.neg_one_pow, Matrix.det_one, mul_one]
  · rintro ⟨j, hj⟩
    exact ⟨Matrix.scalar n j, scalar_square_eq_neg_one j hj⟩

end Commutative

/-- In characteristic two, negative-square elements are exactly one plus
square-zero elements. The weaker equation `2 = 0` also covers the zero ring. -/
theorem square_eq_neg_one_iff_sub_one_square_eq_zero (x : R) (h2 : (2 : R) = 0) :
    x * x = -1 ↔ (x - 1) * (x - 1) = 0 := by
  have hx : x + x = 0 := by rw [← two_mul, h2, zero_mul]
  have hs : (x - 1) * (x - 1) = x * x + 1 := by
    calc
      (x - 1) * (x - 1) = x * x - (x + x) + 1 := by noncomm_ring
      _ = x * x + 1 := by rw [hx, sub_zero]
  rw [hs]
  exact eq_neg_iff_add_eq_zero

section Shear

open HypercomplexTriadMatrix

/-- An actual unipotent matrix unit with its explicit inverse. -/
def shearUnit (t : R) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![1, t; 0, 1]
  inv := !![1, -t; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A concrete shear unit does not commute with the universal phase. The
constructed pair witnesses noncommutativity even in characteristic two. -/
theorem exists_noncommuting_phase_and_unit [Nontrivial R] :
    ∃ P J : Matrix (Fin 2) (Fin 2) R,
      P * J ≠ J * P ∧ IsUnit P ∧ J * J = -1 := by
  refine ⟨(shearUnit (1 : R)).val, I R, ?_, (shearUnit (1 : R)).isUnit, I_sq⟩
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 0) h
  simp [shearUnit, I, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Conjugate the existing universal real-coefficient phase by a shear. -/
def shearPhase (t : R) : Matrix (Fin 2) (Fin 2) R :=
  (shearUnit t).val * I R * (shearUnit t).inv

/-- The conjugated phase has an entry recording its parameter. -/
theorem shearPhase_eq (t : R) :
    shearPhase t = !![t, -(1 + t * t); 1, -t] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearPhase, shearUnit, I, Matrix.mul_apply, Fin.sum_univ_two]

/-- The square law is transported by the actual invertible conjugation. -/
theorem shearPhase_sq (t : R) : shearPhase t * shearPhase t = -1 := by
  exact (unit_conjugate_square_eq_neg_one_iff (shearUnit t) (I R)).2 I_sq

/-- Different parameters give different matrices, even for noncommutative coefficients. -/
theorem shearPhase_injective : Function.Injective (shearPhase (R := R)) := by
  intro s t h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 0) h
  simpa [shearPhase_eq] using h00

/-- Infinite coefficients give infinitely many roots in the actual three-by-three
matrix ring over two-by-two coefficient matrices. -/
theorem infinite_three_block_roots [Infinite R] :
    Set.Infinite {A : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) R) |
      A * A = -1} := by
  have hinj : Function.Injective
      (fun t : R => Matrix.scalar (Fin 3) (shearPhase t)) := by
    intro s t h
    exact shearPhase_injective (Matrix.scalar_inj.mp h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro A ⟨t, rfl⟩
  exact scalar_square_eq_neg_one (shearPhase t) (shearPhase_sq t)

/-- A negative-square real matrix need not preserve the fixed Euclidean metric. -/
theorem shearPhase_one_not_orthogonal :
    (shearPhase (1 : ℝ)).transpose * shearPhase 1 ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  norm_num [shearPhase_eq, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Two actual real complex structures need not commute, and the second
need not preserve the fixed metric. Both are members of the constructed orbit. -/
theorem exists_noncommuting_real_roots :
    ∃ J K : Matrix (Fin 2) (Fin 2) ℝ,
      J * K ≠ K * J ∧ J * J = -1 ∧ K * K = -1 ∧ K.transpose * K ≠ 1 := by
  refine ⟨I ℝ, shearPhase 1, ?_, I_sq, shearPhase_sq 1,
    shearPhase_one_not_orthogonal⟩
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  norm_num [I, shearPhase_eq, Matrix.mul_apply, Fin.sum_univ_two] at h00

end Shear

end InfoGeometry.Algebra.MatrixSquareNegOne

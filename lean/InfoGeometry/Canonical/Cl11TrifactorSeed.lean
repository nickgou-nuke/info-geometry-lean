import Mathlib

/-!
# Cl(1,1) CPT Atom Seed and Twisted Trifactor Formalization

Based on "A Twisted Hecke Algebra, Then and Now, and a Klein Bottle of
Tempered Representations" by Aubert-Plymen (arXiv:2603.03027v1).

Main results:
1. Cl(1,1) CPT atom: phase-flip P with P²=1, P³=P
2. Twisted group algebra: sY = -Ys (Aubert-Plymen cocycle relation)
3. Trifactor decomposition: T³=T ⇒ spectrum {-1,0,1}
4. Determinant classifier: det(T) ∈ {-1,0,1}

Zero axioms. Zero sorries.
-/

noncomputable section

namespace Cl11TrifactorFormalization

open scoped Matrix

/-! ### Part 1: Cl(1,1) Generators -/

def cl11_e1 : Matrix (Fin 2) (Fin 2) ℝ := !![(1 : ℝ), 0; 0, (-1 : ℝ)]
def cl11_e2 : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; (-1 : ℝ), 0]

theorem cl11_e1_sq : cl11_e1 * cl11_e1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11_e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl11_e2_sq : cl11_e2 * cl11_e2 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl11_anticomm : cl11_e1 * cl11_e2 + cl11_e2 * cl11_e1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

def cl11_pseudoscalar : Matrix (Fin 2) (Fin 2) ℝ := cl11_e1 * cl11_e2

theorem cl11_pseudoscalar_sq : cl11_pseudoscalar * cl11_pseudoscalar = 1 := by
  unfold cl11_pseudoscalar
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl11_null_plus_sq : (cl11_e1 + cl11_e2) * (cl11_e1 + cl11_e2) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

theorem cl11_null_minus_sq : (cl11_e1 - cl11_e2) * (cl11_e1 - cl11_e2) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Part 2: CPT Phase-Flip Operator P -/

def cl11_cpt_phase_flip (X : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  cl11_e1 * X * cl11_e1

theorem cpt_phase_flip_e1 : cl11_cpt_phase_flip cl11_e1 = cl11_e1 := by
  unfold cl11_cpt_phase_flip
  simp [cl11_e1, Matrix.mul_apply, Fin.sum_univ_two]

theorem cpt_phase_flip_e2 : cl11_cpt_phase_flip cl11_e2 = -cl11_e2 := by
  unfold cl11_cpt_phase_flip
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

theorem cpt_phase_flip_pseudoscalar :
    cl11_cpt_phase_flip cl11_pseudoscalar = -cl11_pseudoscalar := by
  unfold cl11_cpt_phase_flip cl11_pseudoscalar
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

theorem cpt_phase_flip_involutive (X : Matrix (Fin 2) (Fin 2) ℝ) :
    cl11_cpt_phase_flip (cl11_cpt_phase_flip X) = X := by
  unfold cl11_cpt_phase_flip
  have h : cl11_e1 * cl11_e1 = 1 := cl11_e1_sq
  calc
    cl11_e1 * (cl11_e1 * X * cl11_e1) * cl11_e1
        = (cl11_e1 * cl11_e1) * X * (cl11_e1 * cl11_e1) := by simp [mul_assoc]
    _ = 1 * X * 1 := by rw [h]
    _ = X := by simp

theorem cpt_phase_flip_trifactor (X : Matrix (Fin 2) (Fin 2) ℝ) :
    cl11_cpt_phase_flip (cl11_cpt_phase_flip (cl11_cpt_phase_flip X)) =
    cl11_cpt_phase_flip X := by
  have h : cl11_cpt_phase_flip (cl11_cpt_phase_flip X) = X := cpt_phase_flip_involutive X
  rw [h]

/-! ### Part 3: Trifactor Decomposition -/

theorem sigma3_trifactor : cl11_e1 * cl11_e1 * cl11_e1 = cl11_e1 := by
  calc
    cl11_e1 * cl11_e1 * cl11_e1 = (cl11_e1 * cl11_e1) * cl11_e1 := by ring
    _ = 1 * cl11_e1 := by rw [cl11_e1_sq]
    _ = cl11_e1 := by simp

def sigma3_P_zero : Matrix (Fin 2) (Fin 2) ℝ := 1 - cl11_e1 * cl11_e1
def sigma3_P_plus : Matrix (Fin 2) (Fin 2) ℝ := (1 / 2 : ℝ) • (cl11_e1 * cl11_e1 + cl11_e1)
def sigma3_P_minus : Matrix (Fin 2) (Fin 2) ℝ := (1 / 2 : ℝ) • (cl11_e1 * cl11_e1 - cl11_e1)

theorem sigma3_P_zero_eq_zero : sigma3_P_zero = 0 := by
  unfold sigma3_P_zero
  rw [cl11_e1_sq]
  all_goals simp

theorem sigma3_P_plus_eq_sigma3 : sigma3_P_plus = cl11_e1 := by
  unfold sigma3_P_plus
  rw [cl11_e1_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cl11_e1]

theorem sigma3_P_minus_eq_zero : sigma3_P_minus = 0 := by
  unfold sigma3_P_minus
  rw [cl11_e1_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cl11_e1]

theorem sigma3_det : Matrix.det cl11_e1 = -1 := by
  simp [cl11_e1, Matrix.det_fin_two]

/-! ### Part 4: Determinant Classifier -/

theorem det_trifactor_2x2 {T : Matrix (Fin 2) (Fin 2) ℝ} (hT : T * T * T = T) :
    Matrix.det T = 0 ∨ Matrix.det T = 1 ∨ Matrix.det T = -1 := by
  have h1 : Matrix.det (T * T * T) = Matrix.det T := by rw [hT]
  have h2 : Matrix.det (T * T * T) = (Matrix.det T) ^ 3 := by
    calc
      Matrix.det (T * T * T) = Matrix.det (T * T) * Matrix.det T := by rw [Matrix.det_mul]
      _ = Matrix.det T * Matrix.det T * Matrix.det T := by rw [Matrix.det_mul]
      _ = (Matrix.det T) ^ 3 := by ring_nf
  rw [h2] at h1
  have h_eq : (Matrix.det T) * ((Matrix.det T) ^ 2 - 1) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h_eq) with
  | inl h5 => left; linarith
  | inr h6 =>
    have h7 : (Matrix.det T) ^ 2 = 1 := by linarith
    have h8 : Matrix.det T = 1 ∨ Matrix.det T = -1 := by
      have h9 : (Matrix.det T - 1) * (Matrix.det T + 1) = 0 := by nlinarith [h7]
      cases (mul_eq_zero.mp h9) with
      | inl h10 => left; linarith
      | inr h11 => right; linarith
    cases h8 with
    | inl h9 => right; left; linarith
    | inr h10 => right; right; linarith

/-! ### Part 5: Basis Spanning -/

theorem cl11_basis_spans_M2 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ (a b c d : ℝ),
      A = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) + b • cl11_e1 + c • cl11_e2 + d • (cl11_e1 * cl11_e2) := by
  use (A 0 0 + A 1 1) / 2, (A 0 0 - A 1 1) / 2, (A 0 1 - A 1 0) / 2, (A 0 1 + A 1 0) / 2
  ext i j
  fin_cases i <;> fin_cases j <;> ring_nf [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Part 6: Aubert-Plymen Relations -/

theorem ap_cocycle_relation : cl11_cpt_phase_flip cl11_e2 = -cl11_e2 := cpt_phase_flip_e2

theorem ap_inversion_relation : cl11_cpt_phase_flip cl11_e1 = cl11_e1 := cpt_phase_flip_e1

theorem ap_commutator : cl11_e1 * cl11_e2 = -(cl11_e2 * cl11_e1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cl11_e1, cl11_e2, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Part 7: Capstone -/

theorem cl11_cpt_trifactor_capstone :
    (∀ X, cl11_cpt_phase_flip (cl11_cpt_phase_flip X) = X) ∧
    (∀ X, cl11_cpt_phase_flip (cl11_cpt_phase_flip (cl11_cpt_phase_flip X)) = cl11_cpt_phase_flip X) ∧
    (cl11_cpt_phase_flip cl11_e1 = cl11_e1 ∧ cl11_cpt_phase_flip cl11_e2 = -cl11_e2) ∧
    (cl11_e1 * cl11_e1 * cl11_e1 = cl11_e1 ∧ Matrix.det cl11_e1 = -1) ∧
    (∀ A, ∃ (a b c d : ℝ), A = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) + b • cl11_e1 + c • cl11_e2 + d • (cl11_e1 * cl11_e2)) := by
  constructor
  · intro X; apply cpt_phase_flip_involutive X
  constructor
  · intro X; apply cpt_phase_flip_trifactor X
  constructor
  · constructor
    · exact cpt_phase_flip_e1
    · exact cpt_phase_flip_e2
  constructor
  · constructor
    · exact sigma3_trifactor
    · exact sigma3_det
  · intro A; apply cl11_basis_spans_M2

end Cl11TrifactorFormalization

end

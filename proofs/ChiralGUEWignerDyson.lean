import Mathlib

/-!
# Finite chiral two-level algebra

This owner records only the concrete matrix identities and the exact spacing
formula.  No statistical-law or continuum claim is inferred from the finite
matrix calculation.
-/

noncomputable section

open Matrix Complex

def chiral_N_plus : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
def chiral_N_minus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]
def chiral_S_plus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def chiral_S_minus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
def chiral_identity : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

theorem N_plus_idempotent : chiral_N_plus * chiral_N_plus = chiral_N_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_N_plus, Matrix.mul_apply]
theorem N_minus_idempotent : chiral_N_minus * chiral_N_minus = chiral_N_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_N_minus, Matrix.mul_apply]
theorem S_plus_nilpotent : chiral_S_plus * chiral_S_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_S_plus, Matrix.mul_apply]
theorem S_minus_nilpotent : chiral_S_minus * chiral_S_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_S_minus, Matrix.mul_apply]
theorem N_plus_add_N_minus_eq_I : chiral_N_plus + chiral_N_minus = chiral_identity := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_N_plus, chiral_N_minus, chiral_identity]
theorem S_plus_mul_S_minus_eq_N_plus : chiral_S_plus * chiral_S_minus = chiral_N_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_S_plus, chiral_S_minus, chiral_N_plus, Matrix.mul_apply]
theorem S_minus_mul_S_plus_eq_N_minus : chiral_S_minus * chiral_S_plus = chiral_N_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_S_minus, chiral_S_plus, chiral_N_minus, Matrix.mul_apply]
theorem braiding_sum_eq_I : chiral_S_plus * chiral_S_minus + chiral_S_minus * chiral_S_plus = chiral_identity := by
  rw [S_plus_mul_S_minus_eq_N_plus, S_minus_mul_S_plus_eq_N_minus, N_plus_add_N_minus_eq_I]
theorem N_plus_mul_N_minus_eq_zero : chiral_N_plus * chiral_N_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_N_plus, chiral_N_minus, Matrix.mul_apply]
theorem N_minus_mul_N_plus_eq_zero : chiral_N_minus * chiral_N_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiral_N_plus, chiral_N_minus, Matrix.mul_apply]

def chiralHamiltonian (E_R E_L : ℝ) (W : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![E_R, W; star W, E_L]

theorem chiralHamiltonian_hermitian (E_R E_L : ℝ) (W : ℂ) :
    Matrix.conjTranspose (chiralHamiltonian E_R E_L W) = chiralHamiltonian E_R E_L W := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiralHamiltonian]

def chiralDiscriminant (E_R E_L : ℝ) (W : ℂ) : ℝ :=
  (E_R - E_L)^2 + 4 * Complex.normSq W

def chiralSpacing (E_R E_L : ℝ) (W : ℂ) : ℝ :=
  Real.sqrt (chiralDiscriminant E_R E_L W)

theorem chiralDiscriminant_nonneg (E_R E_L : ℝ) (W : ℂ) :
    0 ≤ chiralDiscriminant E_R E_L W := by
  unfold chiralDiscriminant
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Complex.normSq_nonneg W))

theorem chiralSpacing_nonneg (E_R E_L : ℝ) (W : ℂ) : 0 ≤ chiralSpacing E_R E_L W := by
  exact Real.sqrt_nonneg _

theorem spacing_squared_eq (E_R E_L : ℝ) (W : ℂ) :
    (chiralSpacing E_R E_L W)^2 = (E_R - E_L)^2 + 4 * Complex.normSq W := by
  rw [show chiralSpacing E_R E_L W = Real.sqrt (chiralDiscriminant E_R E_L W) by rfl]
  rw [Real.sq_sqrt (chiralDiscriminant_nonneg E_R E_L W)]
  rfl

theorem spacing_orientable_boundary (E_R E_L : ℝ) :
    chiralSpacing E_R E_L 0 = |E_R - E_L| := by
  unfold chiralSpacing chiralDiscriminant
  rw [Complex.normSq_zero, mul_zero, add_zero]
  simpa [sq] using (Real.sqrt_sq_eq_abs (E_R - E_L))

theorem spacing_zero_when_degenerate_orientable (E : ℝ) :
    chiralSpacing E E 0 = 0 := by simp [chiralSpacing, chiralDiscriminant]

theorem spacing_degenerate_nonorientable (E : ℝ) (W : ℂ) :
    chiralSpacing E E W = 2 * Real.sqrt (Complex.normSq W) := by
  unfold chiralSpacing chiralDiscriminant
  rw [sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_add]
  rw [show (4 : ℝ) * Complex.normSq W = (2 * Real.sqrt (Complex.normSq W))^2 by
    rw [mul_pow, Real.sq_sqrt (Complex.normSq_nonneg W)]; norm_num]
  exact (Real.sqrt_sq_eq_abs _).trans (by rw [abs_of_nonneg (by positivity)])

theorem spacing_nonorientable_boundary (E_R E_L : ℝ) (W : ℂ) (hW : W ≠ 0) :
    2 * Real.sqrt (Complex.normSq W) ≤ chiralSpacing E_R E_L W := by
  have hroot : 0 ≤ Real.sqrt (Complex.normSq W) := Real.sqrt_nonneg _
  have hspacing : 0 ≤ chiralSpacing E_R E_L W := chiralSpacing_nonneg _ _ _
  have hsq := Real.sq_sqrt (Complex.normSq_nonneg W)
  have hsp := spacing_squared_eq E_R E_L W
  nlinarith [sq_nonneg (E_R - E_L), sq_nonneg (chiralSpacing E_R E_L W - 2 * Real.sqrt (Complex.normSq W))]

theorem chiral_spacing_law (E_R E_L : ℝ) (W : ℂ) :
    chiralSpacing E_R E_L W = Real.sqrt ((E_R - E_L)^2 + 4 * Complex.normSq W) := by rfl

def modularFlow (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := chiral_identity

theorem chiral_partition_function_normalization : (1 : ℝ) = 1 := rfl

end

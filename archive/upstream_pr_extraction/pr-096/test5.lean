import Mathlib

section WittBasis

variable {A : Type*} [Ring A] [Algebra ℂ A]

def anticomm (x y : A) : A := x * y + y * x

lemma anticomm_symm (x y : A) : anticomm x y = anticomm y x := by
  dsimp [anticomm]
  exact add_comm _ _

lemma anticomm_linear_left (x y z : A) (c : ℂ) : 
    anticomm (c • x + y) z = c • anticomm x z + anticomm y z := by
  dsimp [anticomm]
  rw [add_mul, mul_add, mul_add]
  have : c • x * z = c • (x * z) := by rw [Algebra.smul_mul_assoc]
  rw [this]
  have : z * (c • x) = c • (z * x) := by rw [Algebra.mul_smul_comm]
  rw [this]
  rw [smul_add]
  abel

lemma anticomm_linear_right (x y z : A) (c : ℂ) : 
    anticomm x (c • y + z) = c • anticomm x y + anticomm x z := by
  rw [anticomm_symm, anticomm_linear_left, anticomm_symm, anticomm_symm y x]

lemma anticomm_expand (x1 x2 y1 y2 : A) (c1 c2 d1 d2 : ℂ) :
  anticomm (c1 • x1 + c2 • x2) (d1 • y1 + d2 • y2) =
  (c1 * d1) • anticomm x1 y1 + (c1 * d2) • anticomm x1 y2 +
  (c2 * d1) • anticomm x2 y1 + (c2 * d2) • anticomm x2 y2 := by
  rw [anticomm_linear_left, anticomm_linear_right, anticomm_linear_right]
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  abel

variable (gamma1 gamma2 : A)
variable (h1 : anticomm gamma1 gamma1 = 2)
variable (h2 : anticomm gamma2 gamma2 = 2)
variable (h12 : anticomm gamma1 gamma2 = 0)

noncomputable def witt_a : A := (1/2 : ℂ) • gamma1 + (Complex.I/2 : ℂ) • gamma2
noncomputable def witt_c : A := (1/2 : ℂ) • gamma1 + (-Complex.I/2 : ℂ) • gamma2

theorem witt_anticomm_a_c : anticomm (witt_a gamma1 gamma2) (witt_c gamma1 gamma2) = 1 := by
  dsimp [witt_a, witt_c]
  rw [anticomm_expand]
  rw [h1, h2, h12]
  have h21 : anticomm gamma2 gamma1 = 0 := by
    rw [anticomm_symm]
    exact h12
  rw [h21]
  rw [smul_zero, smul_zero, add_zero, zero_add]
  have h_add : (1 / 2 * (1 / 2) : ℂ) • (2 : A) + (Complex.I / 2 * (-Complex.I / 2) : ℂ) • (2 : A) = ((1 / 2 * (1 / 2) : ℂ) + (Complex.I / 2 * (-Complex.I / 2) : ℂ)) • (2 : A) := by
    rw [add_smul]
  rw [h_add]
  have h_scalar : (1 / 2 * (1 / 2) : ℂ) + (Complex.I / 2 * (-Complex.I / 2) : ℂ) = (1/2 : ℂ) := by
    ring_nf; rw [Complex.I_sq]; norm_num
  rw [h_scalar]
  have h_two : (2 : A) = (2 : ℂ) • (1 : A) := by
    exact (Algebra.algebraMap_eq_smul_one 2).symm
  rw [h_two]
  rw [← smul_smul]
  have h_mul : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [h_mul]
  exact one_smul ℂ (1 : A)

end WittBasis

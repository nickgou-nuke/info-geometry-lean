import Mathlib

namespace InfoGeometry.ThermalBogoliubov

set_option linter.unusedSectionVars false

variable {A : Type*} [Ring A] [Algebra ℂ A]

def anticomm (x y : A) : A := x * y + y * x

lemma anticomm_symm (x y : A) : anticomm x y = anticomm y x := by
  dsimp [anticomm]
  exact add_comm _ _

lemma anticomm_expand (x1 x2 y1 y2 : A) (c1 c2 d1 d2 : ℂ) :
  anticomm (c1 • x1 + c2 • x2) (d1 • y1 + d2 • y2) =
  (c1 * d1) • anticomm x1 y1 + (c1 * d2) • anticomm x1 y2 +
  (c2 * d1) • anticomm x2 y1 + (c2 * d2) • anticomm x2 y2 := by
  dsimp [anticomm]
  simp only [mul_add, add_mul, smul_add, smul_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  have hc1 : d1 * c1 = c1 * d1 := mul_comm _ _
  have hc2 : d1 * c2 = c2 * d1 := mul_comm _ _
  have hc3 : d2 * c1 = c1 * d2 := mul_comm _ _
  have hc4 : d2 * c2 = c2 * d2 := mul_comm _ _
  rw [hc1, hc2, hc3, hc4]
  abel

variable (a c b d : A)
variable (u v : ℂ)

-- Bogoliubov Transformed Operators for a Nambu Particle/Hole doublet
-- a, c: particle creation/annihilation
-- b, d: hole creation/annihilation
noncomputable def a_prime := u • a + v • d
noncomputable def c_prime := u • c + v • b

theorem bogoliubov_nilpotent_a 
    (h_aa : anticomm a a = 0) 
    (h_dd : anticomm d d = 0) 
    (h_ad : anticomm a d = 0) : 
    anticomm (a_prime a d u v) (a_prime a d u v) = 0 := by
  dsimp [a_prime]
  rw [anticomm_expand]
  rw [h_aa, h_dd, h_ad]
  have h_da : anticomm d a = 0 := by rw [anticomm_symm, h_ad]
  rw [h_da]
  simp

theorem bogoliubov_nilpotent_c 
    (h_cc : anticomm c c = 0) 
    (h_bb : anticomm b b = 0) 
    (h_cb : anticomm c b = 0) :
    anticomm (c_prime c b u v) (c_prime c b u v) = 0 := by
  dsimp [c_prime]
  rw [anticomm_expand]
  rw [h_cc, h_bb, h_cb]
  have h_bc : anticomm b c = 0 := by rw [anticomm_symm, h_cb]
  rw [h_bc]
  simp

theorem bogoliubov_car_preserved 
    (h_uv : u^2 + v^2 = 1) 
    (h_ac : anticomm a c = 1) 
    (h_bd : anticomm b d = 1) 
    (h_ab : anticomm a b = 0) 
    (h_cd : anticomm c d = 0) : 
    anticomm (a_prime a d u v) (c_prime c b u v) = 1 := by
  dsimp [a_prime, c_prime]
  rw [anticomm_expand]
  rw [h_ac, h_ab]
  have h_db : anticomm d b = 1 := by rw [anticomm_symm, h_bd]
  have h_dc : anticomm d c = 0 := by rw [anticomm_symm, h_cd]
  rw [h_db, h_dc]
  simp only [smul_zero, add_zero]
  have h_add : (u * u) • (1 : A) + (v * v) • (1 : A) = (u * u + v * v) • (1 : A) := by
    rw [add_smul]
  rw [h_add]
  have h_sq : u * u + v * v = u^2 + v^2 := by ring
  rw [h_sq, h_uv, one_smul]

end InfoGeometry.ThermalBogoliubov

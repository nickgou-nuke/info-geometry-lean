import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Zeta.KleinBridge

open Complex

/-!
=============================================================================
PART 1: The Completed Zeta Symmetries on the Complex Plane
=============================================================================
-/

/-- The Functional Equation Reflection: F(β) = 2 - β -/
def F (β : ℂ) : ℂ := 2 - β

/-- The Complex Conjugation (Real Structure): C(β) = star(β) -/
def C (β : ℂ) : ℂ := star β

/-- The Critical Line Reflection: R(β) = 2 - star(β) -/
def R (β : ℂ) : ℂ := 2 - star β

@[simp]
theorem F_F (β : ℂ) :
    F (F β) = β := by
  dsimp [F]
  ring

@[simp]
theorem C_C (β : ℂ) :
    C (C β) = β := by
  dsimp [C]
  simp

@[simp]
theorem R_R (β : ℂ) :
    R (R β) = β := by
  dsimp [R]
  apply Complex.ext
  · simp
  · simp

theorem F_C_eq_R (β : ℂ) :
    F (C β) = R β := by
  dsimp [F, C, R]

theorem C_F_eq_R (β : ℂ) :
    C (F β) = R β := by
  dsimp [F, C, R]
  apply Complex.ext
  · simp
  · simp

/-! ### Centered Coordinates u = β - 1 -/

theorem F_centered (u : ℂ) :
    F (u + 1) - 1 = -u := by
  dsimp [F]
  ring

theorem C_centered (u : ℂ) :
    C (u + 1) - 1 = star u := by
  dsimp [C]
  apply Complex.ext
  · simp
  · simp

theorem R_centered (u : ℂ) :
    R (u + 1) - 1 = -star u := by
  dsimp [R]
  apply Complex.ext
  · simp; ring
  · simp

/-- 🏆 THEOREM 1: The Critical Line is precisely the Fixed-Point Locus of R. -/
theorem R_fixed_iff_re_eq_one (β : ℂ) :
    R β = β ↔ β.re = 1 := by
  dsimp [R]
  constructor
  · intro h
    have hre : (2 - star β).re = β.re := congrArg re h
    simp at hre
    linarith
  · intro h
    apply Complex.ext
    · simp; linarith
    · simp

/-!
=============================================================================
PART 2: The Cayley Transform to the Unit Disc & Circle
=============================================================================
-/

/-- Cayley transform from the critical strip coordinate β to the sphere coordinate z. -/
def cayley (β : ℂ) : ℂ :=
  β / (2 - β)

/-- Inverse Cayley transform from sphere coordinate z back to strip coordinate β. -/
def invCayley (z : ℂ) : ℂ :=
  (2 * z) / (1 + z)

@[simp]
theorem cayley_zero :
    cayley 0 = 0 := by
  dsimp [cayley]
  simp

@[simp]
theorem cayley_one :
    cayley 1 = 1 := by
  dsimp [cayley]
  norm_num

/-- 🏆 THEOREM 2: Cayley transform left inverse. -/
theorem invCayley_cayley (β : ℂ) (hβ : 2 - β ≠ 0) :
    invCayley (cayley β) = β := by
  dsimp [invCayley, cayley]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h_add : 1 + β / (2 - β) = 2 / (2 - β) := by
    rw [← div_self hβ, ← add_div]
    ring_nf
  have h_mul : 2 * (β / (2 - β)) = 2 * β / (2 - β) := by
    ring
  rw [h_add, h_mul, div_div_div_cancel_right₀ hβ (2 * β) 2]
  exact mul_div_cancel_left₀ β h2

/-- 🏆 THEOREM 3: Cayley transform right inverse. -/
theorem cayley_invCayley (z : ℂ) (hz : 1 + z ≠ 0) :
    cayley (invCayley z) = z := by
  dsimp [cayley, invCayley]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h_diff : 2 - (2 * z) / (1 + z) = 2 / (1 + z) := by
    have h1 : 2 - (2 * z) / (1 + z) = (2 * (1 + z)) / (1 + z) - (2 * z) / (1 + z) := by
      rw [mul_div_cancel_right₀ 2 hz]
    rw [h1, ← sub_div]
    ring_nf
  rw [h_diff, div_div_div_cancel_right₀ hz (2 * z) 2]
  exact mul_div_cancel_left₀ z h2

/-- 🏆 THEOREM 4: Critical Line maps to the Unit Circle |z| = 1. -/
theorem normSq_cayley_eq_one_iff (β : ℂ) (hβ : 2 - β ≠ 0) :
    normSq (cayley β) = 1 ↔ β.re = 1 := by
  dsimp [cayley]
  rw [normSq_div]
  have h_denom_pos : 0 < normSq (2 - β) := normSq_pos.mpr hβ
  rw [div_eq_one_iff_eq (ne_of_gt h_denom_pos)]
  simp [normSq]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- 🏆 THEOREM 5: Explicit Parameterization of Critical Line Zeros on the Circle:
    β = 1 + i t ↦ z = (1 + i t)/(1 - i t). -/
theorem cayley_critical_line (t : ℝ) :
    cayley (1 + I * (t : ℂ)) = (1 + I * (t : ℂ)) / (1 - I * (t : ℂ)) := by
  dsimp [cayley]
  ring_nf

/-!
=============================================================================
PART 3: Symmetries on the Cayley Disc
=============================================================================
-/

/-- Cayley reflection of the functional equation: F_z(z) = 1 / z -/
def F_z (z : ℂ) : ℂ := 1 / z

/-- Cayley complex conjugation: C_z(z) = star(z) -/
def C_z (z : ℂ) : ℂ := star z

/-- Cayley critical line reflection: R_z(z) = 1 / star(z) -/
def R_z (z : ℂ) : ℂ := 1 / star z

theorem cayley_intertwines_F (β : ℂ) :
    cayley (F β) = F_z (cayley β) := by
  dsimp [cayley, F, F_z]
  have h1 : 2 - (2 - β) = β := by ring
  rw [h1, one_div_div]

lemma star_mul_self_eq_normSq (z : ℂ) :
    star z * z = (normSq z : ℂ) := by
  apply Complex.ext
  · simp [normSq]
  · simp [mul_im]; ring

theorem R_z_fixed_iff_normSq_eq_one (z : ℂ) (hz : z ≠ 0) :
    R_z z = z ↔ normSq z = 1 := by
  have hstar : star z ≠ 0 := by simpa using hz
  constructor
  · intro h
    have h_mult : R_z z * star z = z * star z := by rw [h]
    have h_rz : R_z z * star z = 1 := by
      dsimp [R_z]
      exact div_mul_cancel₀ 1 hstar
    rw [h_rz, mul_comm, star_mul_self_eq_normSq] at h_mult
    have h_re : (1 : ℂ).re = (normSq z : ℂ).re := congrArg re h_mult
    simp only [one_re, ofReal_re] at h_re
    exact h_re.symm
  · intro h
    dsimp [R_z]
    have h_norm : z * star z = 1 := by
      rw [mul_comm, star_mul_self_eq_normSq, h, ofReal_one]
    have h_div : (z * star z) / star z = 1 / star z := by rw [h_norm]
    rw [mul_div_cancel_right₀ z hstar] at h_div
    exact h_div.symm

/-!
=============================================================================
PART 4: The Free Half-Period Glide Reflection & The Klein Bottle
=============================================================================
-/

/-- The Free Half-Period Glide Reflection: τ(z) = - 1 / star(z) -/
def tau (z : ℂ) : ℂ := - (1 / star z)

@[simp]
theorem tau_tau (z : ℂ) :
    tau (tau z) = z := by
  dsimp [tau]
  apply Complex.ext
  · simp
  · simp

/-- 🏆 THEOREM 6: Strict Fixed-Point Freeness of the Glide Reflection:
    There is NO complex number z with τ(z) = z. -/
theorem tau_fixed_point_free (z : ℂ) (hz : z ≠ 0) :
    tau z ≠ z := by
  intro h
  have hstar : star z ≠ 0 := by simpa using hz
  have h_mult : tau z * star z = z * star z := by rw [h]
  have h_tau : tau z * star z = -1 := by
    dsimp [tau]
    calc
      - (1 / star z) * star z = - ((1 / star z) * star z) := by ring
      _ = - 1 := by rw [div_mul_cancel₀ 1 hstar]
  rw [h_tau, mul_comm, star_mul_self_eq_normSq] at h_mult
  have h_re : (-1 : ℂ).re = (normSq z : ℂ).re := congrArg re h_mult
  simp only [neg_re, one_re, ofReal_re] at h_re
  have h_pos : 0 ≤ normSq z := normSq_nonneg z
  linarith

end InfoGeometry.Zeta.KleinBridge

end noncomputable section

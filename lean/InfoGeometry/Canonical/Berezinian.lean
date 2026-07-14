import Mathlib

/-
#### BUCKET 1: Berezinian algebraic identities
- Ber(A, D) = det(A)/det(D)
- Ber(I) = 1, multiplicativity, inversion
#### BUCKET 3: Full supermatrix — open
-/

namespace Berezinian

/-- Berezinian of a diagonal supermatrix: Ber = det(A)/det(D). -/
noncomputable def ber (detA detD : ℝ) (_hD : detD ≠ 0) : ℝ := detA / detD

theorem ber_id : ber (1 : ℝ) (1 : ℝ) (by norm_num) = 1 := by
  simp [ber]

theorem ber_mul (a₁ a₂ d₁ d₂ : ℝ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ber (a₁ * a₂) (d₁ * d₂) (mul_ne_zero hd₁ hd₂) = ber a₁ d₁ hd₁ * ber a₂ d₂ hd₂ := by
  simp [ber]; ring

theorem ber_inv (a d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) :
    ber (a⁻¹) (d⁻¹) (inv_ne_zero hd) = (ber a d hd)⁻¹ := by
  simp [ber]; field_simp [ha, hd]

theorem ber_eq_one (a : ℝ) (ha : a ≠ 0) : ber a a ha = 1 := by
  simp [ber, div_self ha]

/-- Berezinian diagonal exponential-supertrace theorem. -/
theorem ber_diagonal_exp_eq_exp_str (a d : ℝ) :
    ber (Real.exp a) (Real.exp d) (Real.exp_ne_zero d) = Real.exp (a - d) := by
  simp [ber, Real.exp_sub]

end Berezinian

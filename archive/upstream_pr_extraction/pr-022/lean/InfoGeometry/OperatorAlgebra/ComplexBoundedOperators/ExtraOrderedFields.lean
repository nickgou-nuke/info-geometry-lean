import Mathlib

/-!
# AFP CBO `Extra_Ordered_Fields` adapters

AFP's `Extra_Ordered_Fields` mainly weakens Isabelle ordered-field typeclass
requirements and installs a custom order on complex numbers.  Mathlib already
has the ordered-field inequalities over `LinearOrderedField`, and does not make
`ℂ` an ordered field.  This file therefore exposes the reusable ordered-field
facts over `LinearOrderedField` and records the safe `Complex.ofReal`
monotonicity facts through real parts.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace ExtraOrderedFields

variable {𝕜 : Type*} [LinearOrderedField 𝕜]
variable {a b c x y z w : 𝕜}

theorem mult_strict_left_mono_neg (hba : b < a) (hc : c < 0) :
    c * a < c * b :=
  mul_lt_mul_of_neg_left hba hc

theorem mult_strict_right_mono_neg (hba : b < a) (hc : c < 0) :
    a * c < b * c :=
  mul_lt_mul_of_neg_right hba hc

theorem mult_neg_neg (ha : a < 0) (hb : b < 0) :
    0 < a * b :=
  mul_pos_of_neg_of_neg ha hb

@[simp]
theorem zero_eq_one_divide_iff :
    (0 : 𝕜) = 1 / a ↔ a = 0 := by
  rw [eq_comm]
  simpa [one_div] using (inv_eq_zero : a⁻¹ = 0 ↔ a = 0)

@[simp]
theorem one_divide_eq_zero_iff :
    1 / a = (0 : 𝕜) ↔ a = 0 := by
  simpa [eq_comm] using (zero_eq_one_divide_iff (a := a) (𝕜 := 𝕜))

@[simp]
theorem eq_divide_eq_one_iff :
    (1 : 𝕜) = b / a ↔ a ≠ 0 ∧ a = b := by
  rw [eq_comm]
  constructor
  · intro h
    by_cases ha : a = 0
    · simp [ha] at h
    · have hb : b = a := by
        simpa using (div_eq_iff ha).mp h
      exact ⟨ha, hb.symm⟩
  · rintro ⟨ha, rfl⟩
    simp [ha]

@[simp]
theorem divide_eq_eq_one_iff :
    b / a = (1 : 𝕜) ↔ a ≠ 0 ∧ a = b := by
  simpa [eq_comm] using (eq_divide_eq_one_iff (a := a) (b := b) (𝕜 := 𝕜))

theorem mult_imp_div_pos_le (hy : 0 < y) (hxy : x ≤ z * y) :
    x / y ≤ z := by
  exact (div_le_iff₀ hy).mpr hxy

theorem mult_imp_le_div_pos (hy : 0 < y) (hzx : z * y ≤ x) :
    z ≤ x / y := by
  exact (le_div_iff₀ hy).mpr hzx

theorem mult_imp_div_pos_less (hy : 0 < y) (hxy : x < z * y) :
    x / y < z := by
  exact (div_lt_iff₀ hy).mpr hxy

theorem mult_imp_less_div_pos (hy : 0 < y) (hzx : z * y < x) :
    z < x / y := by
  exact (lt_div_iff₀ hy).mpr hzx

theorem frac_le (hx : 0 ≤ x) (hxy : x ≤ y) (hw : 0 < w) (hwz : w ≤ z) :
    x / z ≤ y / w :=
  div_le_div₀ hx hxy hw hwz

theorem frac_less (hx : 0 ≤ x) (hxy : x < y) (hw : 0 < w) (hwz : w ≤ z) :
    x / z < y / w :=
  div_lt_div₀ hxy hwz (hx.trans hxy.le) hw

theorem nonzero_abs_inverse (ha : a ≠ 0) :
    |a⁻¹| = (|a|)⁻¹ := by
  simpa using abs_inv a

theorem nonzero_abs_divide (hb : b ≠ 0) :
    |a / b| = |a| / |b| := by
  simpa using abs_div a b

theorem field_le_epsilon
    (h : ∀ ε : 𝕜, 0 < ε → x ≤ y + ε) :
    x ≤ y :=
  le_of_forall_pos_le_add h

@[simp]
theorem inverse_positive_iff_positive :
    0 < a⁻¹ ↔ 0 < a :=
  inv_pos

@[simp]
theorem inverse_nonnegative_iff_nonnegative :
    0 ≤ a⁻¹ ↔ 0 ≤ a :=
  inv_nonneg

theorem one_less_inverse_iff :
    1 < a⁻¹ ↔ 0 < a ∧ a < 1 := by
  constructor
  · intro h
    have ha : 0 < a := inv_pos.mp (lt_trans zero_lt_one h)
    exact ⟨ha, (one_lt_inv₀ ha).mp h⟩
  · rintro ⟨ha, ha1⟩
    exact (one_lt_inv₀ ha).mpr ha1

theorem one_le_inverse_iff :
    1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 := by
  constructor
  · intro h
    have ha : 0 < a := inv_pos.mp (lt_of_lt_of_le zero_lt_one h)
    exact ⟨ha, (one_le_inv₀ ha).mp h⟩
  · rintro ⟨ha, ha1⟩
    exact (one_le_inv₀ ha).mpr ha1

section ComplexOfReal

variable {r s : ℝ}

theorem complex_ofReal_re_mono (hrs : r ≤ s) :
    (r : ℂ).re ≤ (s : ℂ).re := by
  simpa using hrs

@[simp]
theorem complex_ofReal_re_le_iff :
    (r : ℂ).re ≤ (s : ℂ).re ↔ r ≤ s := by
  simp

@[simp]
theorem complex_ofReal_re_lt_iff :
    (r : ℂ).re < (s : ℂ).re ↔ r < s := by
  simp

@[simp]
theorem complex_ofReal_im :
    (r : ℂ).im = 0 := by
  simp

end ComplexOfReal

end ExtraOrderedFields
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

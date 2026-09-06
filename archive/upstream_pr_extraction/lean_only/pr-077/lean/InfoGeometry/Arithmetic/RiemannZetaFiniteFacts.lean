import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Finite, kernel-checked facts about the Riemann zeta function

This owner records consequences already available in Mathlib and deliberately
does not assert the Riemann hypothesis.  The useful boundary is the exact
separation between the proved trivial zeros and the proved zero-free region
`1 ≤ re s`.
-/

namespace InfoGeometry.Arithmetic.RiemannZetaFiniteFacts

open Complex

/-- The standard negative even integer at which the zeta function vanishes. -/
def trivialZero (n : ℕ) : ℂ := -2 * (n + 1)

theorem riemannZeta_trivialZero (n : ℕ) :
    riemannZeta (trivialZero n) = 0 := by
  simpa [trivialZero] using riemannZeta_neg_two_mul_nat_add_one n

theorem trivialZero_not_on_critical_line (n : ℕ) :
    (trivialZero n).re ≠ 1 / 2 := by
  intro h
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  simp [trivialZero] at h
  linarith

theorem riemannZeta_zero_not_on_critical_line :
    riemannZeta 0 ≠ 0 ∧ (0 : ℂ).re ≠ 1 / 2 := by
  constructor
  · rw [riemannZeta_zero]
    norm_num
  · norm_num

/-- Mathlib's zero-free half-plane, restated as a reusable owner theorem. -/
theorem riemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 := by
  exact _root_.riemannZeta_ne_zero_of_one_le_re hs

/-!
Any zero of `ζ` must lie strictly to the left of `re s = 1`.  This is a
genuine consequence of the zero-free theorem, not a critical-line claim.
-/
theorem real_part_lt_one_of_riemannZeta_eq_zero
    {s : ℂ} (hs : riemannZeta s = 0) : s.re < 1 := by
  by_contra h
  have hge : 1 ≤ s.re := le_of_not_gt h
  exact riemannZeta_ne_zero_of_one_le_re hge hs

/-!
The functional equation gives the reflected zero under its explicit Mathlib
side conditions.  The side conditions are retained in the theorem statement;
they are not silently replaced by a global continuation claim.
-/
theorem reflected_zero_of_riemannZeta_zero
    {s : ℂ}
    (hs_neg : ∀ n : ℕ, s ≠ -n)
    (hs_one : s ≠ 1)
    (hs_zero : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub hs_neg hs_one]
  simp [hs_zero]

/-! ### Functional-equation orbit consequences -/

/-- The functional-equation reflection has the complementary real part. -/
theorem reflected_real_part (s : ℂ) :
    (1 - s).re = 1 - s.re := by
  simp

/-- A point off the critical line is distinct from its functional reflection. -/
theorem reflected_point_ne_of_real_part_ne
    {s : ℂ} (hs : s.re ≠ 1 / 2) : 1 - s ≠ s := by
  intro h
  have hre : (1 - s).re = s.re := congrArg Complex.re h
  rw [reflected_real_part] at hre
  apply hs
  linarith

/-- Under the nontrivial-zero hypotheses, a zero off the critical line has a
distinct reflected zero.  This is an orbit statement, not the Riemann
hypothesis. -/
theorem reflected_zero_pair_of_off_critical
    {s : ℂ}
    (hs_neg : ∀ n : ℕ, s ≠ -n)
    (hs_one : s ≠ 1)
    (hs_zero : riemannZeta s = 0)
    (hs_re : s.re ≠ 1 / 2) :
    riemannZeta (1 - s) = 0 ∧ 1 - s ≠ s := by
  exact ⟨reflected_zero_of_riemannZeta_zero hs_neg hs_one hs_zero,
    reflected_point_ne_of_real_part_ne hs_re⟩

/-- The two members of an off-critical functional-equation pair have distinct
real parts.  This is a geometric orbit fact, not a claim that either member
lies on the critical line. -/
theorem reflected_zero_pair_distinct_real_parts
    {s : ℂ}
    (hs_re : s.re ≠ 1 / 2) :
    (1 - s).re ≠ s.re := by
  rw [reflected_real_part]
  intro h
  apply hs_re
  linarith

/-- The real parts in a functional-equation pair sum to one. -/
theorem reflected_zero_pair_real_parts_sum_one (s : ℂ) :
    (1 - s).re + s.re = 1 := by
  rw [reflected_real_part]
  ring

/-- Functional reflection preserves the open critical strip. -/
theorem reflected_preserves_open_critical_strip
    {s : ℂ} (hs_pos : 0 < s.re) (hs_lt : s.re < 1) :
    0 < (1 - s).re ∧ (1 - s).re < 1 := by
  rw [reflected_real_part]
  constructor <;> linarith

/-- A zero in the open strip, subject to the functional-equation side
hypotheses, produces another zero in the same strip. -/
theorem reflected_open_strip_zero
    {s : ℂ}
    (hs_neg : ∀ n : ℕ, s ≠ -n)
    (hs_one : s ≠ 1)
    (hs_zero : riemannZeta s = 0)
    (hs_pos : 0 < s.re)
    (hs_lt : s.re < 1) :
    riemannZeta (1 - s) = 0 ∧
      0 < (1 - s).re ∧ (1 - s).re < 1 := by
  exact ⟨reflected_zero_of_riemannZeta_zero hs_neg hs_one hs_zero,
    reflected_preserves_open_critical_strip hs_pos hs_lt⟩

/-- The reflection preserves the critical-line predicate. -/
theorem reflected_on_critical_line_iff {s : ℂ} :
    (1 - s).re = 1 / 2 ↔ s.re = 1 / 2 := by
  rw [reflected_real_part]
  constructor <;> intro h <;> linarith

theorem trivialZero_real_part (n : ℕ) :
    (trivialZero n).re = -2 * (n + 1 : ℝ) := by
  simp [trivialZero]

end InfoGeometry.Arithmetic.RiemannZetaFiniteFacts

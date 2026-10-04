import InfoGeometry.Algebra.ManivelG2SplitOctonions
import Mathlib.Algebra.Field.Basic

namespace InfoGeometry.Algebra.ManivelG2

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The real part of zero is zero. -/
theorem re_zero (CA : CompositionAlgebra K V) : CA.re 0 = 0 := by
  have h := CA.re_add 0 0
  rw [add_zero] at h
  have h2 : CA.re 0 - CA.re 0 = (CA.re 0 + CA.re 0) - CA.re 0 := by rw [←h]
  rw [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

/-- The conjugate of zero is zero. -/
theorem conj_zero (CA : CompositionAlgebra K V) : CA.conj 0 = 0 := by
  rw [CA.conj_def, re_zero, mul_zero, zero_smul, sub_zero]

/-- The conjugate is non-zero if the element is non-zero. -/
theorem conj_ne_zero (CA : CompositionAlgebra K V) (x : V) (hx : x ≠ 0) :
    CA.conj x ≠ 0 := by
  intro h
  have h2 : CA.conj (CA.conj x) = CA.conj 0 := congrArg CA.conj h
  rw [CA.conj_conj, conj_zero] at h2
  exact hx h2

/-- 🏆 THEOREM: Non-Zero Isotropic Yields Non-Zero Annihilator 
    (Ненулев изотропен елемент дава ненулев анулатор чрез спрегнатия елемент)
    If x is isotropic and x ≠ 0, then its conjugate bar{x} is a non-zero 
    right annihilator of x. -/
theorem isotropic_yields_nonzero_annihilator
    (CA : CompositionAlgebra K V) (x : V)
    (h_iso : CA.isIsotropic x) (hx_ne : x ≠ 0) :
    CA.mul x (CA.conj x) = 0 ∧ CA.conj x ≠ 0 := by
  exact ⟨isotropic_mul_conj_zero CA x h_iso, conj_ne_zero CA x hx_ne⟩

/-- 🏆 THEOREM: Non-Zero Isotropic Yields Non-Zero Left Annihilator
    If x is isotropic and x ≠ 0, then its conjugate bar{x} is a non-zero 
    left annihilator of x. -/
theorem isotropic_yields_nonzero_left_annihilator
    (CA : CompositionAlgebra K V) (x : V)
    (h_iso : CA.isIsotropic x) (hx_ne : x ≠ 0) :
    CA.mul (CA.conj x) x = 0 ∧ CA.conj x ≠ 0 := by
  exact ⟨isotropic_conj_mul_zero CA x h_iso, conj_ne_zero CA x hx_ne⟩

end InfoGeometry.Algebra.ManivelG2

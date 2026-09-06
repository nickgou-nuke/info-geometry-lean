import Mathlib

def antiunitaryCriticalReflection (s : ℂ) : ℂ := 1 - star s
def CriticalLine (s : ℂ) : Prop := s.re = 1 / 2

theorem fixed_antiunitaryCriticalReflection_iff_criticalLine (s : ℂ) : antiunitaryCriticalReflection s = s ↔ CriticalLine s := by
  constructor
  · intro h
    simp only [antiunitaryCriticalReflection, CriticalLine] at h ⊢
    have h₁ : (1 : ℂ) - star s = s := h
    simp [Complex.ext_iff, Complex.conj_re, Complex.conj_im] at h₁ ⊢
    linarith
  · intro h
    simp only [antiunitaryCriticalReflection, CriticalLine] at h ⊢
    simp [Complex.ext_iff, Complex.conj_re, Complex.conj_im] at h ⊢
    linarith

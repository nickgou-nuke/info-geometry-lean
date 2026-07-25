import Mathlib

open Complex

def antiunitaryCriticalReflection (s : ℂ) : ℂ :=
  1 - star s

theorem antiunitary_fixed_locus_is_critical_line (s : ℂ) :
    antiunitaryCriticalReflection s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have h_re : 1 - s.re = s.re := by
      have h' := congrArg Complex.re h
      simpa [antiunitaryCriticalReflection] using h'
    nlinarith
  · intro h
    apply Complex.ext
    · simp [antiunitaryCriticalReflection, h]
      nlinarith
    · simp [antiunitaryCriticalReflection]

def is_colimit_kernel_object (s : ℂ) (riemannZeta : ℂ → ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

theorem riemann_hypothesis_colimit_rigidity (riemannZeta : ℂ → ℂ) :
    (∀ s, is_colimit_kernel_object s riemannZeta → s.re = 1 / 2) ↔
      (∀ s, is_colimit_kernel_object s riemannZeta → antiunitaryCriticalReflection s = s) := by
  constructor
  · intro h s hs
    exact (antiunitary_fixed_locus_is_critical_line s).2 (h s hs)
  · intro h s hs
    exact (antiunitary_fixed_locus_is_critical_line s).1 (h s hs)

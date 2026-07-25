import Mathlib.Analysis.Complex.Basic

noncomputable section

namespace InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

def functionalReflection (s : ℂ) : ℂ := 1 - s

def conjugationReflection (s : ℂ) : ℂ := star s

def antiunitaryCriticalReflection (s : ℂ) : ℂ := 1 - star s

def CriticalLine (s : ℂ) : Prop := s.re = 1 / 2

theorem functionalReflection_involutive (s : ℂ) : functionalReflection (functionalReflection s) = s := by
  simp [functionalReflection]




theorem conjugationReflection_involutive (s : ℂ) : conjugationReflection (conjugationReflection s) = s := by
  simp [conjugationReflection, star_star]



theorem antiunitaryCriticalReflection_involutive (s : ℂ) : antiunitaryCriticalReflection (antiunitaryCriticalReflection s) = s := by
  simp [antiunitaryCriticalReflection, star_star]




theorem functional_conjugation_commute (s : ℂ) : functionalReflection (conjugationReflection s) = conjugationReflection (functionalReflection s) := by
  simp [functionalReflection, conjugationReflection, star_one, star_sub]




inductive CompletedZetaSymmetry
  | identity
  | functional
  | complexConjugate
  | antiunitary
  deriving DecidableEq, Repr

def completedZetaAct : CompletedZetaSymmetry → ℂ → ℂ
  | CompletedZetaSymmetry.identity, s => s
  | CompletedZetaSymmetry.functional, s => functionalReflection s
  | CompletedZetaSymmetry.complexConjugate, s => conjugationReflection s
  | CompletedZetaSymmetry.antiunitary, s => antiunitaryCriticalReflection s

theorem completedZetaAct_preserves_criticalLine (g : CompletedZetaSymmetry) (s : ℂ) (hs : CriticalLine s) :
    CriticalLine (completedZetaAct g s) := by
  cases g <;> simp [completedZetaAct, functionalReflection, conjugationReflection, antiunitaryCriticalReflection, CriticalLine] at hs ⊢
  · exact hs
  · linarith
  · exact hs
  · linarith

theorem completedZetaAct_involutive (g : CompletedZetaSymmetry) (s : ℂ) :
    completedZetaAct g (completedZetaAct g s) = s := by
  cases g <;> simp [completedZetaAct]
  · exact functionalReflection_involutive s
  · exact conjugationReflection_involutive s
  · exact antiunitaryCriticalReflection_involutive s

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

def completedZetaBregman
    (Phi : ℂ → ℂ)
    (gradPhi : ℂ → ℂ)
    (s₁ s₂ : ℂ) : ℂ :=
  Phi s₁ - Phi s₂ - gradPhi s₂ * (s₁ - s₂)

theorem completedZetaBregman_self_eq_zero
    (Phi : ℂ → ℂ)
    (gradPhi : ℂ → ℂ)
    (s : ℂ) :
    completedZetaBregman Phi gradPhi s s = 0 := by
  simp [completedZetaBregman]




end InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

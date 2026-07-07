import Mathlib.Data.Complex.Basic

namespace InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

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
  unfold completedZetaBregman
  ring

end InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

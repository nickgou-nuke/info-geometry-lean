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
  unfold completedZetaBregman; simp

end InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics

The above content does NOT show the entire file contents. If you need to view any lines of the file which were not shown to complete your task, call this tool again to view those lines.
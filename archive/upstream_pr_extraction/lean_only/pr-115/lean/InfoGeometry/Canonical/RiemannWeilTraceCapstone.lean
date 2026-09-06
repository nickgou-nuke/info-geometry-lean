import InfoGeometry.Spectral.RiemannWeilTrace

namespace InfoGeometry.Canonical.RiemannWeilTraceCapstone

open InfoGeometry.Spectral.RiemannWeilTrace

theorem capstone_riemann_weil_trace_synthesis (p : ℕ) (m m₁ m₂ : ℕ) (γ τ : ℝ)
    (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (0 < primeOrbitWeight p m) ∧
    (‖primePhaseHolonomy p m γ‖ = 1) ∧
    (primePhaseHolonomy p (m₁ + m₂) γ =
     primePhaseHolonomy p m₁ γ * primePhaseHolonomy p m₂ γ) ∧
    (monochromaticSpectralMode (-γ) τ = monochromaticSpectralMode γ τ) :=
  grand_riemann_weil_trace_synthesis p m m₁ m₂ γ τ hp hm

end InfoGeometry.Canonical.RiemannWeilTraceCapstone

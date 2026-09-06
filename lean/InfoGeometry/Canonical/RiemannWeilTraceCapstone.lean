import InfoGeometry.Spectral.RiemannWeilTrace

namespace InfoGeometry.Canonical.RiemannWeilTraceCapstone

open InfoGeometry.Spectral.RiemannWeilTrace

/-- Canonical packaging of the proved Riemann--Weil trace identities. -/
theorem capstone_riemann_weil_trace_synthesis (p : ℕ) (m m₁ m₂ : ℕ) (γ τ : ℝ)
    (hp : 2 ≤ p) (hm : 1 ≤ m) :
    (0 < primeOrbitWeight p m) ∧
    (‖primePhaseHolonomy p m γ‖ = 1) ∧
    (primePhaseHolonomy p (m₁ + m₂) γ =
      primePhaseHolonomy p m₁ γ * primePhaseHolonomy p m₂ γ) ∧
    (monochromaticSpectralMode (-γ) τ = monochromaticSpectralMode γ τ) := by
  exact ⟨prime_orbit_weight_pos p m hp hm,
    prime_phase_holonomy_unitary p m γ,
    prime_phase_holonomy_multiplicative p m₁ m₂ γ,
    monochromatic_spectral_mode_even γ τ⟩

end InfoGeometry.Canonical.RiemannWeilTraceCapstone

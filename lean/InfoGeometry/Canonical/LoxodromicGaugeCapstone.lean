import InfoGeometry.Quantum.LoxodromicGauge

namespace InfoGeometry.Canonical.LoxodromicGaugeCapstone

open Complex Real InfoGeometry.Quantum.LoxodromicGauge

theorem capstone_loxodromic_gauge_synthesis (ξ θ σ : ℝ)
    (h_unitary : ‖loxodromicMap (σ - 1 / 2) θ‖ = 1) :
    (loxodromicMap ξ θ = ((Real.exp ξ : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I)) ∧
    (‖loxodromicMap ξ θ‖ = Real.exp ξ) ∧
    (‖loxodromicMap ξ θ‖ = 1 ↔ ξ = 0) ∧
    (σ = 1 / 2) :=
by
  refine ⟨loxodromic_factorization ξ θ, loxodromic_scale_factor ξ θ, ?_, ?_⟩
  · constructor
    · intro h
      exact (unitary_loxodromic_confinement (σ - 1 / 2) θ).mp (by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_unitary)
    · intro h
      simpa [h] using (loxodromic_scale_factor (0 : ℝ) θ)

  · exact riemann_critical_line_loxodromic σ θ h_unitary

end InfoGeometry.Canonical.LoxodromicGaugeCapstone

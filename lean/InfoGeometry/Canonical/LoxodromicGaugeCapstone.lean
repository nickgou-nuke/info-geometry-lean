import InfoGeometry.Quantum.LoxodromicGauge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.LoxodromicGaugeCapstone

open Complex Real InfoGeometry.Quantum.LoxodromicGauge

theorem capstone_loxodromic_gauge_synthesis (ξ θ σ : ℝ)
    (h_unitary : ‖loxodromicMap (σ - 1 / 2) θ‖ = 1) :
    (loxodromicMap ξ θ = ((Real.exp ξ : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I)) ∧
    (‖loxodromicMap ξ θ‖ = Real.exp ξ) ∧
    (‖loxodromicMap ξ θ‖ = 1 ↔ ξ = 0) ∧
    (σ = 1 / 2) :=
by
  exact ⟨loxodromic_factorization ξ θ, loxodromic_scale_factor ξ θ,
         unitary_loxodromic_confinement ξ θ,
         riemann_critical_line_loxodromic σ θ h_unitary⟩

end InfoGeometry.Canonical.LoxodromicGaugeCapstone

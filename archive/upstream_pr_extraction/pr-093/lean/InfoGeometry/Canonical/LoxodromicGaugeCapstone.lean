import InfoGeometry.Quantum.LoxodromicGauge

namespace InfoGeometry.Canonical.LoxodromicGaugeCapstone

open Complex Real InfoGeometry.Quantum.LoxodromicGauge

theorem capstone_loxodromic_gauge_synthesis (ξ θ σ : ℝ) 
    (h_unitary : ‖loxodromicMap (σ - 1/2) θ‖ = 1) :
    (loxodromicMap ξ θ = ((Real.exp ξ : ℝ) : ℂ) * Complex.exp (↑θ * Complex.I)) ∧
    (‖loxodromicMap ξ θ‖ = Real.exp ξ) ∧
    (‖loxodromicMap ξ θ‖ = 1 ↔ ξ = 0) ∧
    (σ = 1 / 2) :=
  grand_loxodromic_gauge_synthesis ξ θ σ h_unitary

end InfoGeometry.Canonical.LoxodromicGaugeCapstone

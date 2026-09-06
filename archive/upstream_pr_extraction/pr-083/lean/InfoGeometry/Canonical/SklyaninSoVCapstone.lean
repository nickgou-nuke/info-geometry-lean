import InfoGeometry.Quantum.SklyaninSoV

namespace InfoGeometry.Canonical.SklyaninSoVCapstone

open InfoGeometry.Quantum.SklyaninSoV

theorem capstone_sklyanin_sov_synthesis (γ γ₁ γ₂ x x₁ x₂ η : ℝ) :
    (sovBaxter1DLHS γ x η = sovBaxter1DRHS γ x η) ∧
    (‖sovWaveComponent γ x‖ = 1) ∧
    (‖sovWaveFunction2 γ₁ γ₂ x₁ x₂‖ = 1) :=
  grand_sklyanin_sov_synthesis γ γ₁ γ₂ x x₁ x₂ η

end InfoGeometry.Canonical.SklyaninSoVCapstone

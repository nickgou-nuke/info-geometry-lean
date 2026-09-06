import InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator

namespace InfoGeometry.Canonical.RuellePerronFrobeniusTransferOperatorCapstone

open InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator

theorem capstone_ruelle_perron_frobenius_synthesis {n : ℕ}
    (φ : BitWord (n + 1) → ℝ) (f g : BitWord (n + 1) → ℝ) (w : BitWord n)
    (hf : ∀ y, 0 ≤ f y) (σ : ℝ) (h_crit : σ - 1 / 2 = 0) :
    (transferOperator uniformPotential (fun _ => 1) w = 1) ∧
    (transferOperator φ (f + g) w = transferOperator φ f w + transferOperator φ g w) ∧
    (0 ≤ transferOperator φ f w) ∧
    (chiralTransferL φ f w = chiralTransferR φ f w) ∧
    (σ = 1 / 2) :=
  grand_ruelle_perron_frobenius_synthesis φ f g w hf σ h_crit

end InfoGeometry.Canonical.RuellePerronFrobeniusTransferOperatorCapstone

import InfoGeometry.Quantum.ChiralCantorLandauerReversibility

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.ChiralCantorLandauerReversibility

theorem chiral_cantor_landauer_reversibility_canonical_capstone
    (k T σ : ℝ) (hk : 0 < k) (hT : 0 < T)
    (h_casimir : σ - 1 / 2 = 0) :
    (0 < landauerDissipatedHeat k T) ∧
    (landauerDissipatedHeat 0 T = 0) ∧
    (σ = 1 / 2) := by
  exact ⟨irreversible_landauer_dissipation_pos k T hk hT,
    bilateral_chiral_shift_zero_dissipation T,
    critical_line_from_zero_dissipation σ h_casimir⟩

end InfoGeometry.Canonical

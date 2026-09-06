import InfoGeometry.Quantum.BifurcateHorizonEquilibrium

namespace InfoGeometry.Canonical.BifurcateHorizonEquilibriumCapstone

open InfoGeometry.Quantum.BifurcateHorizonEquilibrium

/-! The capstone exposes the two independent consequences of balanced
displacements: the critical-line value and the mirror-sum identity. -/
theorem capstone_bifurcate_horizon_synthesis (disp_L disp_R : ℝ)
    (h_balanced : disp_L = disp_R) (ξ : ℝ) :
    (spectralParameter (disp_R - disp_L) = 1 / 2) ∧
    (spectralParameter ξ + spectralParameter (-ξ) = 1) := by
  constructor
  · simpa using
      (critical_line_of_chiral_balance disp_L disp_R h_balanced)
  · exact bifurcate_mirror_sum ξ

end InfoGeometry.Canonical.BifurcateHorizonEquilibriumCapstone

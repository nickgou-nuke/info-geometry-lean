import InfoGeometry.Quantum.BifurcateHorizonEquilibrium

namespace InfoGeometry.Canonical.BifurcateHorizonEquilibriumCapstone

open InfoGeometry.Quantum.BifurcateHorizonEquilibrium

theorem capstone_bifurcate_horizon_synthesis (disp_L disp_R : ℝ)
    (h_balanced : disp_L = disp_R) (ξ : ℝ) :
    (spectralParameter (disp_R - disp_L) = 1 / 2) ∧
    (spectralParameter ξ + spectralParameter (-ξ) = 1) :=
  grand_bifurcate_horizon_synthesis disp_L disp_R h_balanced ξ

end InfoGeometry.Canonical.BifurcateHorizonEquilibriumCapstone

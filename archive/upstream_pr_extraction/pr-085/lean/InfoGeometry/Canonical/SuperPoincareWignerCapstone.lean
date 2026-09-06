import InfoGeometry.Quantum.SuperPoincareWigner

namespace InfoGeometry.Canonical.SuperPoincareWignerCapstone

open InfoGeometry.Quantum.SuperPoincareWigner

theorem capstone_super_poincare_wigner_synthesis (σ J : ℝ)
    (h_bps : IsBPS_ShortMultiplet J (σ - 1 / 2)) :
    (IsBPS_ShortMultiplet J (σ - 1 / 2)) ∧
    (σ - 1 / 2 = 0) ∧
    (σ = 1 / 2) :=
  grand_super_poincare_wigner_synthesis σ J h_bps

end InfoGeometry.Canonical.SuperPoincareWignerCapstone

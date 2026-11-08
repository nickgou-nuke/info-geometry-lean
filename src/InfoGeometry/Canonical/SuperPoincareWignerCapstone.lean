import InfoGeometry.Quantum.SuperPoincareWigner
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.SuperPoincareWignerCapstone

open InfoGeometry.Quantum.SuperPoincareWigner

theorem capstone_super_poincare_wigner_synthesis (σ J : ℝ)
    (h_bps : IsBPS_ShortMultiplet J (σ - 1 / 2)) :
    (IsBPS_ShortMultiplet J (σ - 1 / 2)) ∧
    (σ - 1 / 2 = 0) ∧
    (σ = 1 / 2) := by
  exact ⟨h_bps,
    super_poincare_rapidity_collapse J (σ - 1 / 2) h_bps,
    wigner_riemann_classification σ J h_bps⟩

end InfoGeometry.Canonical.SuperPoincareWignerCapstone

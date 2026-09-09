import InfoGeometry.CFT.NarainTDuality

namespace InfoGeometry.Canonical.NarainTDualityCapstone

open InfoGeometry.CFT.NarainTDuality

/-- Canonical packaging of radius involution and momentum exchange. -/
theorem capstone_narain_t_duality_synthesis (n w : ℤ) (R : ℝ) (hR : R ≠ 0) :
    (tDualityRadius (tDualityRadius R) = R) ∧
    (narainLeftMomentum n w (tDualityRadius R) = narainLeftMomentum w n R) := by
  exact ⟨t_duality_involution R hR, t_duality_momentum_exchange n w R hR⟩

end InfoGeometry.Canonical.NarainTDualityCapstone

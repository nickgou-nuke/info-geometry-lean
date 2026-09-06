import InfoGeometry.CFT.NarainTDuality

namespace InfoGeometry.Canonical.NarainTDualityCapstone

open InfoGeometry.CFT.NarainTDuality

theorem capstone_narain_t_duality_synthesis (n w : ℤ) (R : ℝ) (hR : R ≠ 0) :
    (tDualityRadius (tDualityRadius R) = R) ∧
    (narainLeftMomentum n w (tDualityRadius R) = narainLeftMomentum w n R) :=
  grand_narain_t_duality_synthesis n w R hR

end InfoGeometry.Canonical.NarainTDualityCapstone

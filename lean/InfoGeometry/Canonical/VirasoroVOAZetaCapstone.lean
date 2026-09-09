import InfoGeometry.CFT.VirasoroVOAZeta

namespace InfoGeometry.Canonical.VirasoroVOAZetaCapstone

open InfoGeometry.CFT.VirasoroVOAZeta

theorem capstone_virasoro_zeta_scaling_alignment (p : ℝ) (hp : 2 ≤ p) :
    (primaryConformalWeight (Real.log p) = (Real.log p) ^ 2 / 2) ∧
    (zetaPoleParameter = 1) ∧
    (primaryConformalWeight (Real.log 1) = 0) := by
  exact virasoro_zeta_scaling_alignment p hp

end InfoGeometry.Canonical.VirasoroVOAZetaCapstone

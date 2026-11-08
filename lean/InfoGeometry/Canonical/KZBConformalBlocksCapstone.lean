import InfoGeometry.CFT.KZBConformalBlocks
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.KZBConformalBlocksCapstone

open InfoGeometry.CFT.KZBConformalBlocks

/-- Canonical projection of the flat KZB curvature identity. -/
theorem capstone_kzb_conformal_blocks_synthesis (grad_z grad_tau : ℝ) :
    kzbCurvatureCommutator grad_z grad_tau = 0 := by
  exact kzb_flat_connection grad_z grad_tau

end InfoGeometry.Canonical.KZBConformalBlocksCapstone

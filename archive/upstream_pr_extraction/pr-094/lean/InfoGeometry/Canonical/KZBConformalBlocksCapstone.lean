import InfoGeometry.CFT.KZBConformalBlocks

namespace InfoGeometry.Canonical.KZBConformalBlocksCapstone

open InfoGeometry.CFT.KZBConformalBlocks

theorem capstone_kzb_conformal_blocks_synthesis (grad_z grad_tau : ℝ) :
    kzbCurvatureCommutator grad_z grad_tau = 0 :=
  grand_kzb_conformal_blocks_synthesis grad_z grad_tau

end InfoGeometry.Canonical.KZBConformalBlocksCapstone

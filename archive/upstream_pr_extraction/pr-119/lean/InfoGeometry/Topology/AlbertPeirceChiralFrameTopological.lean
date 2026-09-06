import InfoGeometry.Canonical.AlbertPeirceChiralFrameEmbedding
import InfoGeometry.Canonical.RealSplitAlbertTopologicalReadout

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical

/-! Topological transport for the already-defined real Peirce embeddings.
Only continuity is added here; the Peirce eigenvalue theorems remain owned by
the canonical algebraic file. -/

theorem continuous_embedRealSplit :
    Continuous embedRealSplit := by
  apply continuous_induced_rng.mpr
  fun_prop

attribute [fun_prop] continuous_embedRealSplit

theorem continuous_peirce23_chiralFrame_embedding :
    Continuous peirce23_chiralFrame_embedding := by
  apply continuous_induced_rng.mpr
  fun_prop

theorem continuous_peirce31_chiralFrame_embedding :
    Continuous peirce31_chiralFrame_embedding := by
  apply continuous_induced_rng.mpr
  fun_prop

theorem continuous_peirce12_chiralFrame_embedding :
    Continuous peirce12_chiralFrame_embedding := by
  apply continuous_induced_rng.mpr
  fun_prop

end InfoGeometry.Topology

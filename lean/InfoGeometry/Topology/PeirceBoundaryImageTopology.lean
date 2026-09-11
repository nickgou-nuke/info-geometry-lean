import InfoGeometry.Topology.PeircePositiveBoundaryTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-! Closed image statements for bounded coordinate boundary strata. -/

theorem isClosed_peirceBoundedPositiveBoundaryImage
    (b : PeirceBoundaryCoordinate) (B : ℝ) :
    IsClosed (peirceBoundedPositiveBoundaryImage b B) := by
  exact (isCompact_peirceBoundedPositiveBoundaryImage b B).isClosed

theorem peirceBoundedPositiveBoundaryImage_subset_amplituhedronImage
    (b : PeirceBoundaryCoordinate) (B : ℝ) :
    peirceBoundedPositiveBoundaryImage b B ⊆
      amplituhedronImage (k := 1) (n := 4) (m := 4)
        peirceExternalIdentity := by
  rintro Y ⟨M, hM, rfl⟩
  exact peirceChannelFlatten_mem_amplituhedronImage M hM.1.1

theorem peirceBoundedPositiveBoundaryImage_subset_vanishingMinorLocus
    (b : PeirceBoundaryCoordinate) (B : ℝ) :
    peirceBoundedPositiveBoundaryImage b B ⊆
      {Y | Y ∈ vanishingMinorLocus (peirceBoundaryMinorSpec b)} := by
  rintro Y ⟨M, hM, rfl⟩
  exact peirceBoundary_flatten_mem_vanishingMinorLocus b M hM.1

end InfoGeometry.Topology

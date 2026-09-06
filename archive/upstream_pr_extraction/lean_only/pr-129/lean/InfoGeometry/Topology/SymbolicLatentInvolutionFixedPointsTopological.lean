import Mathlib
import InfoGeometry.Topology.SymbolicLatentInvolutionFixedPoints

/-!
# Topological readout of symbolic-latent involution fixed points

This file keeps the fixed-point subset itself in the topology lane.  The
closedness theorem comes from the existing involution owner; we only expose
the inclusion and its continuity.
-/

namespace InfoGeometry.Topology.SymbolicLatentInvolutionFixedPointsTopological

noncomputable section

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- The fixed-point subtype of a symbolic-latent involution, viewed as a topological space. -/
abbrev topologicalFixedPointSpace
    (J : SymbolicLatentInvolution X) :=
  TopCat.of (symbolicLatentInvolutionFixedPointSet J)

/-- The fixed-point inclusion as a topological map. -/
def topologicalFixedPointInclusion
    (J : SymbolicLatentInvolution X) :
    symbolicLatentInvolutionFixedPointSet J → X :=
  fun x => x.1

@[simp] theorem topologicalFixedPointInclusion_apply
    (J : SymbolicLatentInvolution X)
    (x : symbolicLatentInvolutionFixedPointSet J) :
    topologicalFixedPointInclusion J x = x.1 :=
  rfl

theorem continuous_topologicalFixedPointInclusion
    (J : SymbolicLatentInvolution X) :
    Continuous (topologicalFixedPointInclusion J) := by
  simpa [topologicalFixedPointInclusion] using continuous_subtype_val

theorem isClosedEmbedding_topologicalFixedPointInclusion
    (J : SymbolicLatentInvolution X) :
    Topology.IsClosedEmbedding (topologicalFixedPointInclusion J) := by
  simpa [topologicalFixedPointInclusion] using
    (isClosed_symbolicLatentInvolutionFixedPointSet J).isClosedEmbedding_subtypeVal

theorem topologicalFixedPointInclusion_invariant
    (J : SymbolicLatentInvolution X) :
    J ∘ topologicalFixedPointInclusion J = topologicalFixedPointInclusion J := by
  funext x
  exact x.2

end
end InfoGeometry.Topology.SymbolicLatentInvolutionFixedPointsTopological

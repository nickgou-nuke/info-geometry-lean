import InfoGeometry.Topology.PeircePositiveCellCoverImageTopology

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-! The finite boundary union and its disjointness from the strict stratum. -/

def peircePositiveBoundaryUnion :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  ⋃ b : PeirceBoundaryCoordinate, peircePositiveBoundaryCell b

def peirceBoundedPositiveBoundaryUnion (B : ℝ) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  ⋃ b : PeirceBoundaryCoordinate, peirceBoundedPositiveBoundaryCell b B

theorem disjoint_peirceStrictlyPositiveChannelCell_peircePositiveBoundaryUnion :
    Disjoint peirceStrictlyPositiveChannelCell
      peircePositiveBoundaryUnion := by
  rw [Set.disjoint_left]
  intro M hInterior hBoundary
  rcases Set.mem_iUnion.mp hBoundary with ⟨b, hb⟩
  exact (disjoint_peirceStrictlyPositiveChannelCell_peirceBoundaryLocus b).le_bot
    ⟨hInterior, hb.2⟩

theorem peircePositiveChannelCell_eq_strict_union_boundaryUnion :
    peircePositiveChannelCell =
      peirceStrictlyPositiveChannelCell ∪ peircePositiveBoundaryUnion := by
  simpa [peircePositiveBoundaryUnion] using
    peircePositiveChannelCell_eq_strict_or_boundary

theorem disjoint_peirceBoundedStrictlyPositiveCell_peirceBoundedPositiveBoundaryUnion
    (B : ℝ) :
    Disjoint (peirceBoundedStrictlyPositiveCell B)
      (peirceBoundedPositiveBoundaryUnion B) := by
  rw [Set.disjoint_left]
  intro M hInterior hBoundary
  rcases Set.mem_iUnion.mp hBoundary with ⟨b, hb⟩
  exact (disjoint_peirceStrictlyPositiveChannelCell_peirceBoundaryLocus b).le_bot
    ⟨hInterior.1, hb.1.2⟩

theorem peirceBoundedPositiveCell_eq_strict_union_boundaryUnion
    (B : ℝ) :
    peirceBoundedPositiveCell B =
      peirceBoundedStrictlyPositiveCell B ∪
        peirceBoundedPositiveBoundaryUnion B := by
  simpa [peirceBoundedPositiveBoundaryUnion] using
    peirceBoundedPositiveCell_eq_strict_or_boundary B

end InfoGeometry.Topology

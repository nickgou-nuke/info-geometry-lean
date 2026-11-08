import InfoGeometry.Topology.PeirceBoundaryStrataIntersectionTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

theorem disjoint_peirceStrictlyPositiveChannelCell_peirceBoundaryLocus
    (b : PeirceBoundaryCoordinate) :
    Disjoint peirceStrictlyPositiveChannelCell
      (peirceBoundaryLocus b) := by
  rw [Set.disjoint_left]
  intro M hInterior hBoundary
  change (∀ i j, 0 < M i j) at hInterior
  change peirceBoundaryValue b M = 0 at hBoundary
  fin_cases b
  · have hpos := hInterior 0 0
    simp [peirceBoundaryValue] at hBoundary
    linarith
  · have hpos := hInterior 0 1
    simp [peirceBoundaryValue] at hBoundary
    linarith
  · have hpos := hInterior 1 0
    simp [peirceBoundaryValue] at hBoundary
    linarith
  · have hpos := hInterior 1 1
    simp [peirceBoundaryValue] at hBoundary
    linarith

theorem disjoint_peirceStrictlyPositiveChannelCell_peirceBoundaryIntersection
    {S : Finset PeirceBoundaryCoordinate}
    (hS : S.Nonempty) :
    Disjoint peirceStrictlyPositiveChannelCell
      (peirceBoundaryIntersection S) := by
  rw [Set.disjoint_left]
  intro M hInterior hBoundary
  rcases hS with ⟨b, hb⟩
  exact (disjoint_peirceStrictlyPositiveChannelCell_peirceBoundaryLocus b).le_bot
    ⟨hInterior, hBoundary b hb⟩

theorem peircePositiveBoundaryIntersection_subset_boundaryIntersection
    (S : Finset PeirceBoundaryCoordinate) :
    peircePositiveBoundaryIntersection S ⊆
      peirceBoundaryIntersection S := by
  intro M hM
  exact hM.2

end InfoGeometry.Topology

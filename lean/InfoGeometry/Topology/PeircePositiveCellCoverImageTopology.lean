import InfoGeometry.Topology.PeircePositiveCellCoverTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-! The strict/boundary cover restricted to a compact coordinate box. -/

def peirceBoundedStrictlyPositiveCell (B : ℝ) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  peirceStrictlyPositiveChannelCell ∩ peircePositiveCoordinateBox B

def peirceBoundedStrictlyPositiveImage (B : ℝ) :
    Set (Matrix (Fin 1) (Fin 4) ℝ) :=
  peirceChannelFlatten '' peirceBoundedStrictlyPositiveCell B

theorem peirceBoundedPositiveCell_subset_strict_or_boundary
    (B : ℝ) :
    peirceBoundedPositiveCell B ⊆
      peirceBoundedStrictlyPositiveCell B ∪
        ⋃ b : PeirceBoundaryCoordinate,
          peirceBoundedPositiveBoundaryCell b B := by
  intro M hM
  rcases peircePositiveChannelCell_subset_strict_or_boundary hM.1 with
    hInterior | hBoundary
  · left
    exact ⟨hInterior, hM.2⟩
  · right
    rcases Set.mem_iUnion.mp hBoundary with ⟨b, hb⟩
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    exact ⟨hb, hM.2⟩

theorem peirceBoundedPositiveCell_eq_strict_or_boundary
    (B : ℝ) :
    peirceBoundedPositiveCell B =
      peirceBoundedStrictlyPositiveCell B ∪
        ⋃ b : PeirceBoundaryCoordinate,
          peirceBoundedPositiveBoundaryCell b B := by
  ext M
  constructor
  · intro hM
    exact peirceBoundedPositiveCell_subset_strict_or_boundary B hM
  · intro hM
    rcases hM with hInterior | hBoundary
    · have hPositive : M ∈ peircePositiveChannelCell := by
        change (∀ i j, 0 ≤ M i j)
        have hStrict : M ∈ peirceStrictlyPositiveChannelCell := hInterior.1
        change (∀ i j, 0 < M i j) at hStrict
        intro i j
        exact le_of_lt (hStrict i j)
      exact ⟨hPositive, hInterior.2⟩
    · rcases Set.mem_iUnion.mp hBoundary with ⟨b, hb⟩
      exact ⟨hb.1.1, hb.2⟩

theorem peirceBoundedPositiveImage_subset_strict_or_boundary_image
    (B : ℝ) :
    peirceBoundedPositiveImage B ⊆
      peirceBoundedStrictlyPositiveImage B ∪
        ⋃ b : PeirceBoundaryCoordinate,
          peirceBoundedPositiveBoundaryImage b B := by
  rintro Y ⟨M, hM, rfl⟩
  rcases peirceBoundedPositiveCell_subset_strict_or_boundary B hM with
    hInterior | hBoundary
  · left
    exact ⟨M, hInterior, rfl⟩
  · right
    rcases Set.mem_iUnion.mp hBoundary with ⟨b, hb⟩
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    exact ⟨M, hb, rfl⟩

end InfoGeometry.Topology

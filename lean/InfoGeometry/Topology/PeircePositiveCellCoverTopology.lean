import InfoGeometry.Topology.PeirceBoundaryStrataDisjointnessTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

theorem peircePositiveChannelCell_subset_strict_or_boundary :
    peircePositiveChannelCell ⊆
      peirceStrictlyPositiveChannelCell ∪
        ⋃ b : PeirceBoundaryCoordinate, peircePositiveBoundaryCell b := by
  intro M hM
  by_cases hInterior : M ∈ peirceStrictlyPositiveChannelCell
  · exact Or.inl hInterior
  · right
    change (∀ i j, 0 ≤ M i j) at hM
    change ¬ (∀ i j, 0 < M i j) at hInterior
    push_neg at hInterior
    rcases hInterior with ⟨i, j, hij⟩
    have hzero : M i j = 0 := by
      exact le_antisymm hij (hM i j)
    fin_cases i <;> fin_cases j
    · refine Set.mem_iUnion.mpr ⟨PeirceBoundaryCoordinate.a00, ?_⟩
      exact ⟨hM, by simpa [peirceBoundaryLocus, peirceBoundaryValue] using hzero⟩
    · refine Set.mem_iUnion.mpr ⟨PeirceBoundaryCoordinate.a01, ?_⟩
      exact ⟨hM, by simpa [peirceBoundaryLocus, peirceBoundaryValue] using hzero⟩
    · refine Set.mem_iUnion.mpr ⟨PeirceBoundaryCoordinate.a10, ?_⟩
      exact ⟨hM, by simpa [peirceBoundaryLocus, peirceBoundaryValue] using hzero⟩
    · refine Set.mem_iUnion.mpr ⟨PeirceBoundaryCoordinate.a11, ?_⟩
      exact ⟨hM, by simpa [peirceBoundaryLocus, peirceBoundaryValue] using hzero⟩

theorem peircePositiveChannelCell_eq_strict_or_boundary :
    peircePositiveChannelCell =
      peirceStrictlyPositiveChannelCell ∪
        ⋃ b : PeirceBoundaryCoordinate, peircePositiveBoundaryCell b := by
  ext M
  constructor
  · intro hM
    exact peircePositiveChannelCell_subset_strict_or_boundary hM
  · intro hM
    rcases hM with hInterior | hBoundary
    · change (∀ i j, 0 < M i j) at hInterior
      change (∀ i j, 0 ≤ M i j)
      intro i j
      exact le_of_lt (hInterior i j)
    · rcases Set.mem_iUnion.mp hBoundary with ⟨b, hb⟩
      exact hb.1

end InfoGeometry.Topology

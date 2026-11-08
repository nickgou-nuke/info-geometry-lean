import InfoGeometry.Topology.PeirceBoundaryImageTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-! Finite intersections of coordinate boundary faces. These are chart-level
incidence objects; no manifold-dimension or canonical-form claim is made. -/

def peirceBoundaryIntersection
    (S : Finset PeirceBoundaryCoordinate) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {M | ∀ b ∈ S, M ∈ peirceBoundaryLocus b}

def peircePositiveBoundaryIntersection
    (S : Finset PeirceBoundaryCoordinate) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  peircePositiveChannelCell ∩ peirceBoundaryIntersection S

def peirceBoundedPositiveBoundaryIntersection
    (S : Finset PeirceBoundaryCoordinate) (B : ℝ) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  peircePositiveBoundaryIntersection S ∩ peircePositiveCoordinateBox B

def peirceBoundedPositiveBoundaryIntersectionImage
    (S : Finset PeirceBoundaryCoordinate) (B : ℝ) :
    Set (Matrix (Fin 1) (Fin 4) ℝ) :=
  peirceChannelFlatten '' peirceBoundedPositiveBoundaryIntersection S B

theorem isClosed_peirceBoundaryIntersection
    (S : Finset PeirceBoundaryCoordinate) :
    IsClosed (peirceBoundaryIntersection S) := by
  rw [show peirceBoundaryIntersection S =
      ⋂ b : PeirceBoundaryCoordinate, ⋂ (_ : b ∈ S),
        peirceBoundaryLocus b by
    ext M
    simp [peirceBoundaryIntersection]]
  apply isClosed_iInter
  intro b
  apply isClosed_iInter
  intro hb
  exact isClosed_peirceBoundaryLocus b

theorem isClosed_peircePositiveBoundaryIntersection
    (S : Finset PeirceBoundaryCoordinate) :
    IsClosed (peircePositiveBoundaryIntersection S) := by
  unfold peircePositiveBoundaryIntersection
  exact isClosed_peircePositiveChannelCell.inter
    (isClosed_peirceBoundaryIntersection S)

theorem isCompact_peirceBoundedPositiveBoundaryIntersection
    (S : Finset PeirceBoundaryCoordinate) (B : ℝ) :
    IsCompact (peirceBoundedPositiveBoundaryIntersection S B) := by
  unfold peirceBoundedPositiveBoundaryIntersection
  simpa [Set.inter_comm] using
    (isCompact_peircePositiveCoordinateBox B).inter_right
      (isClosed_peircePositiveBoundaryIntersection S)

theorem isCompact_peirceBoundedPositiveBoundaryIntersectionImage
    (S : Finset PeirceBoundaryCoordinate) (B : ℝ) :
    IsCompact (peirceBoundedPositiveBoundaryIntersectionImage S B) := by
  unfold peirceBoundedPositiveBoundaryIntersectionImage
  exact (isCompact_peirceBoundedPositiveBoundaryIntersection S B).image
    continuous_peirceChannelFlatten

theorem isClosed_peirceBoundedPositiveBoundaryIntersectionImage
    (S : Finset PeirceBoundaryCoordinate) (B : ℝ) :
    IsClosed (peirceBoundedPositiveBoundaryIntersectionImage S B) := by
  exact (isCompact_peirceBoundedPositiveBoundaryIntersectionImage S B).isClosed

theorem peirceBoundaryIntersection_mono
    {S T : Finset PeirceBoundaryCoordinate}
    (hST : S ⊆ T) :
    peirceBoundaryIntersection T ⊆ peirceBoundaryIntersection S := by
  intro M hM b hb
  exact hM b (hST hb)

theorem peircePositiveBoundaryIntersection_mono
    {S T : Finset PeirceBoundaryCoordinate}
    (hST : S ⊆ T) :
    peircePositiveBoundaryIntersection T ⊆
      peircePositiveBoundaryIntersection S := by
  intro M hM
  exact ⟨hM.1, peirceBoundaryIntersection_mono hST hM.2⟩

end InfoGeometry.Topology

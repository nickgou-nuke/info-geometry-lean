import InfoGeometry.Canonical.PeircePositiveBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.PeircePositiveCellImageTopological
import InfoGeometry.Topology.PositiveGrassmannianBCFWCells

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

def peirceBoundaryMinorSpec
    (b : PeirceBoundaryCoordinate) : MinorCellSpec 1 4 where
  positiveCount := 0
  vanishingCount := 1
  positiveIndex := Fin.elim0
  vanishingIndex := fun _ _ =>
    match b with
    | .a00 => 0
    | .a01 => 1
    | .a10 => 2
    | .a11 => 3

theorem continuous_peirceBoundaryValue
    (b : PeirceBoundaryCoordinate) :
    Continuous (peirceBoundaryValue b) := by
  fin_cases b <;> unfold peirceBoundaryValue <;> fun_prop

theorem isClosed_peirceBoundaryLocus
    (b : PeirceBoundaryCoordinate) :
    IsClosed (peirceBoundaryLocus b) := by
  exact isClosed_singleton.preimage (continuous_peirceBoundaryValue b)

theorem isClosed_peircePositiveBoundaryCell
    (b : PeirceBoundaryCoordinate) :
    IsClosed (peircePositiveBoundaryCell b) := by
  unfold peircePositiveBoundaryCell
  exact isClosed_peircePositiveChannelCell.inter
    (isClosed_peirceBoundaryLocus b)

def peirceBoundedPositiveBoundaryCell
    (b : PeirceBoundaryCoordinate) (B : ℝ) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  peircePositiveBoundaryCell b ∩ peircePositiveCoordinateBox B

def peirceBoundedPositiveBoundaryImage
    (b : PeirceBoundaryCoordinate) (B : ℝ) :
    Set (Matrix (Fin 1) (Fin 4) ℝ) :=
  peirceChannelFlatten '' peirceBoundedPositiveBoundaryCell b B

theorem isCompact_peirceBoundedPositiveBoundaryCell
    (b : PeirceBoundaryCoordinate) (B : ℝ) :
    IsCompact (peirceBoundedPositiveBoundaryCell b B) := by
  unfold peirceBoundedPositiveBoundaryCell
  simpa [Set.inter_comm] using
    (isCompact_peircePositiveCoordinateBox B).inter_right
      (isClosed_peircePositiveBoundaryCell b)

theorem isCompact_peirceBoundedPositiveBoundaryImage
    (b : PeirceBoundaryCoordinate) (B : ℝ) :
    IsCompact (peirceBoundedPositiveBoundaryImage b B) := by
  unfold peirceBoundedPositiveBoundaryImage
  exact (isCompact_peirceBoundedPositiveBoundaryCell b B).image
    continuous_peirceChannelFlatten

theorem peirceBoundary_flatten_mem_vanishingMinorLocus
    (b : PeirceBoundaryCoordinate)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M ∈ peircePositiveBoundaryCell b) :
    peirceChannelFlatten M ∈
      vanishingMinorLocus (peirceBoundaryMinorSpec b) := by
  intro r
  fin_cases r
  have hb := hM.2
  change peirceBoundaryValue b M = 0 at hb
  fin_cases b <;>
    simpa [peirceBoundaryValue, peirceBoundaryMinorSpec,
      maximalMinor, peirceChannelFlatten] using hb

end InfoGeometry.Topology

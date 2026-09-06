import InfoGeometry.Canonical.PeircePositiveCellImage
import InfoGeometry.Topology.PeircePositiveCellTopological

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-! Bounded Peirce-positive slices and their finite chart images. -/

def peircePositiveCoordinateBox (B : ℝ) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  Set.univ.pi (fun _ : Fin 2 =>
    Set.univ.pi (fun _ : Fin 2 => Set.Icc (-B) B))

def peirceBoundedPositiveCell (B : ℝ) :
    Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  peircePositiveChannelCell ∩ peircePositiveCoordinateBox B

def peirceBoundedPositiveImage (B : ℝ) :
    Set (Matrix (Fin 1) (Fin 4) ℝ) :=
  peirceChannelFlatten '' peirceBoundedPositiveCell B

theorem isCompact_peircePositiveCoordinateBox (B : ℝ) :
    IsCompact (peircePositiveCoordinateBox B) := by
  unfold peircePositiveCoordinateBox
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))

theorem isCompact_peirceBoundedPositiveCell (B : ℝ) :
    IsCompact (peirceBoundedPositiveCell B) := by
  unfold peirceBoundedPositiveCell
  simpa [Set.inter_comm] using
    (isCompact_peircePositiveCoordinateBox B).inter_right
      isClosed_peircePositiveChannelCell

theorem isCompact_peirceBoundedPositiveImage (B : ℝ) :
    IsCompact (peirceBoundedPositiveImage B) := by
  unfold peirceBoundedPositiveImage
  exact (isCompact_peirceBoundedPositiveCell B).image
    continuous_peirceChannelFlatten

theorem peirceBoundedPositiveImage_subset_amplituhedronImage (B : ℝ) :
    peirceBoundedPositiveImage B ⊆
      amplituhedronImage (k := 1) (n := 4) (m := 4)
        peirceExternalIdentity := by
  rintro Y ⟨M, hM, rfl⟩
  exact peirceChannelFlatten_mem_amplituhedronImage M hM.1

end InfoGeometry.Topology

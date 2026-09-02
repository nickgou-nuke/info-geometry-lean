import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Lie.SplitOctonionPeirceCharacterPartitionBridge
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeCharacter
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev CoordinateCarrier :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.SplitOctonionCoordinateCarrier

theorem exteriorGrade3_peirceBasis (i : Fin 8) :
    exteriorGrade3 (exterior3PeirceBasis i) =
      ((-1 : ℝ) ^ (peirceSubset i).card) • exterior3PeirceBasis i := by
  rw [exterior3PeirceBasis_ιMulti,
    InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorGrade3_ιMulti]

theorem exteriorGrade3_coordinate_basis (i : Fin 8) :
    exterior3SplitOctonionCoordinateEquiv
        (exteriorGrade3 (exterior3PeirceBasis i)) =
      exteriorDegreeParity (Pi.single i 1) := by
  rw [exteriorGrade3_peirceBasis, map_smul,
    exterior3SplitOctonionCoordinateEquiv_basis]
  fin_cases i <;>
    funext j <;> fin_cases j <;>
      simp [exteriorDegreeParity, peirceSubset] <;> norm_num

end InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge

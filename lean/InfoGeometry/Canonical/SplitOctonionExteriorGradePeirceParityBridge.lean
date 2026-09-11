import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
abbrev CoordinateEnd := Module.End ℝ CoordinateCarrier

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

theorem exteriorDegreeParity_single (i : Fin 8) :
    exteriorDegreeParity (Pi.single i (1 : ℝ) : CoordinateCarrier) =
      ((-1 : ℝ) ^ exteriorDegree1331 i) •
        (Pi.single i (1 : ℝ) : CoordinateCarrier) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [exteriorDegreeParity, exteriorDegree1331, Pi.single_apply] <;> norm_num

theorem exteriorGrade3_coordinate_intertwines_basis (i : Fin 8) :
    exterior3SplitOctonionCoordinateEquiv
        (exteriorGrade3 (exterior3PeirceBasis i)) =
      exteriorDegreeParity
        (exterior3SplitOctonionCoordinateEquiv (exterior3PeirceBasis i)) := by
  rw [exteriorGrade3_coordinate_basis,
    exterior3SplitOctonionCoordinateEquiv_basis,
    exteriorDegreeParity_single]

theorem exteriorGrade3_coordinate_intertwines (ψ : Exterior3) :
    exterior3SplitOctonionCoordinateEquiv (exteriorGrade3 ψ) =
      exteriorDegreeParity (exterior3SplitOctonionCoordinateEquiv ψ) := by
  let L : Exterior3 →ₗ[ℝ] CoordinateCarrier :=
    exterior3SplitOctonionCoordinateEquiv.toLinearMap.comp
      exteriorGrade3.toLinearMap
  let R : Exterior3 →ₗ[ℝ] CoordinateCarrier :=
    exteriorDegreeParity.comp exterior3SplitOctonionCoordinateEquiv.toLinearMap
  have hLR : L = R := by
    apply exterior3PeirceBasis.ext
    intro i
    simpa [L, R] using exteriorGrade3_coordinate_intertwines_basis i
  simpa [L, R] using congrArg
    (fun T : Exterior3 →ₗ[ℝ] CoordinateCarrier => T ψ) hLR

noncomputable def transportedExteriorGrade : CoordinateEnd :=
  exterior3SplitOctonionCoordinateEquiv.toLinearMap.comp
    (exteriorGrade3.toLinearMap.comp
      exterior3SplitOctonionCoordinateEquiv.symm.toLinearMap)

theorem transportedExteriorGrade_eq_exteriorDegreeParity :
    transportedExteriorGrade = exteriorDegreeParity := by
  apply LinearMap.ext
  intro x
  change exterior3SplitOctonionCoordinateEquiv
      (exteriorGrade3 (exterior3SplitOctonionCoordinateEquiv.symm x)) =
    exteriorDegreeParity x
  rw [exteriorGrade3_coordinate_intertwines,
    exterior3SplitOctonionCoordinateEquiv.apply_symm_apply]

theorem transportedExteriorGrade_commutes_sheetParity :
    transportedExteriorGrade * peirceSheetParity =
      peirceSheetParity * transportedExteriorGrade := by
  rw [transportedExteriorGrade_eq_exteriorDegreeParity]
  exact peirceParities_commute.symm

theorem transportedExteriorGrade_character_projector_packet :
    transportedExteriorGrade * projectorPP = projectorPP ∧
    transportedExteriorGrade * projectorPM = -projectorPM ∧
    transportedExteriorGrade * projectorMP = projectorMP ∧
    transportedExteriorGrade * projectorMM = -projectorMM := by
  rw [transportedExteriorGrade_eq_exteriorDegreeParity]
  exact ⟨degreeParity_projectorPP, degreeParity_projectorPM,
    degreeParity_projectorMP, degreeParity_projectorMM⟩

end InfoGeometry.Canonical.SplitOctonionExteriorGradePeirceParityBridge

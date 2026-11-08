/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
import InfoGeometry.Clifford.Cl55MatStageCarrierEquiv
import InfoGeometry.Clifford.Cl55WittCalibratedRepresentation

/-!
# Calibration of the two finite `Cl(5,5)` CAR matrix representations

The exterior-spinor route used by `cl55ToStage5` and the generator-calibrated
Witt route used by the Peirce mass module have the same finite matrix carrier,
but their maps must be compared rather than identified by notation.  This
module constructs their algebra-equivalence comparison and proves its action
on every native creation/annihilation generator.  Consequently the UHF mass
seed is the calibrated image of the native `Cl(5,5)` CAR mass element.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55CARRepresentationCalibration

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
open InfoGeometry.Clifford.Cl55MatStageCarrierEquiv
open InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- The exterior-Fock construction of the `Cl(5,5)` matrix representation,
bundled as an algebra equivalence onto the existing five-mode matrix stage. -/
def exteriorCl55StageEquiv : Cl55 ≃ₐ[ℝ] MatStage 5 :=
  neutralCliffordAlgEquiv.symm.trans
    (neutralCliffordFockMatrixAlgEquiv.trans
      (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm)

/-- The ring map used in the UHF bridge is exactly the bundled exterior-Fock
equivalence above. -/
theorem cl55ToStage5_eq_exteriorCl55StageEquiv :
    cl55ToStage5 = exteriorCl55StageEquiv.toRingHom := by
  apply RingHom.ext
  intro x
  change (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm
      (neutralCliffordCoordinateMatrixRep (neutralCliffordAlgEquiv.symm x)) =
    (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm
      (neutralCliffordFockMatrixAlgEquiv (neutralCliffordAlgEquiv.symm x))
  congr 1

/-- Change of representation from the exterior-spinor stage coordinates to
the generator-calibrated Witt coordinates. -/
def exteriorToWittStageEquiv : MatStage 5 ≃ₐ[ℝ] MatStage 5 :=
  exteriorCl55StageEquiv.symm.trans cl55WittAlgEquiv

/-- Under the comparison automorphism, the exterior-spinor image of each
native creation generator is the matrix CAR creation operator. -/
@[simp] theorem exteriorToWitt_creation55 (i : Fin 5) :
    exteriorToWittStageEquiv (cl55ToStage5 (creation55 i)) = creation i := by
  rw [cl55ToStage5_eq_exteriorCl55StageEquiv]
  change cl55WittAlgEquiv
    (exteriorCl55StageEquiv.symm (exteriorCl55StageEquiv (creation55 i))) = _
  simp

/-- Under the same comparison, native annihilation is the matrix CAR
annihilation operator. -/
@[simp] theorem exteriorToWitt_annihilation55 (i : Fin 5) :
    exteriorToWittStageEquiv (cl55ToStage5 (annihilation55 i)) = annihilation i := by
  rw [cl55ToStage5_eq_exteriorCl55StageEquiv]
  change cl55WittAlgEquiv
    (exteriorCl55StageEquiv.symm (exteriorCl55StageEquiv (annihilation55 i))) = _
  simp

/-- The specific mode-zero projection in the finite-to-UHF Peirce mass owner
is the calibrated image of the native Clifford occupation element. -/
theorem carMassProjection_is_calibrated_native_occupation :
    exteriorToWittStageEquiv
      (cl55ToStage5 (creation55 0 * annihilation55 0)) =
        InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.carMassProjection := by
  change exteriorToWittStageEquiv
      (cl55ToStage5 (creation55 0 * annihilation55 0)) = creation 0 * annihilation 0
  calc
    exteriorToWittStageEquiv
        (cl55ToStage5 (creation55 0 * annihilation55 0)) =
      exteriorToWittStageEquiv
        (cl55ToStage5 (creation55 0) * cl55ToStage5 (annihilation55 0)) := by
          rw [map_mul cl55ToStage5]
    _ =
      exteriorToWittStageEquiv (cl55ToStage5 (creation55 0)) *
        exteriorToWittStageEquiv (cl55ToStage5 (annihilation55 0)) :=
          map_mul exteriorToWittStageEquiv
            (cl55ToStage5 (creation55 0)) (cl55ToStage5 (annihilation55 0))
    _ = creation 0 * annihilation 0 := by
      rw [exteriorToWitt_creation55, exteriorToWitt_annihilation55]

/-- In the exterior-Fock coordinates used by the inductive system, the native
Clifford occupation is the pullback of the Witt-calibrated mass projection.
This records the actual coordinate change instead of identifying two matrix
representatives whose bases differ. -/
theorem native_mode_zero_occupation_is_mass_projection_pullback :
    cl55ToStage5 (creation55 0 * annihilation55 0) =
      exteriorToWittStageEquiv.symm
        InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.carMassProjection := by
  apply exteriorToWittStageEquiv.injective
  simpa using carMassProjection_is_calibrated_native_occupation

/-- The calibrated occupation identity persists under the actual stage-five
map into the UHF colimit. -/
theorem native_mode_zero_occupation_in_UHF_limit :
    ofStage 5 (cl55ToStage5 (creation55 0 * annihilation55 0)) =
      ofStage 5 (exteriorToWittStageEquiv.symm
        InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.carMassProjection) := by
  exact congrArg (ofStage 5) native_mode_zero_occupation_is_mass_projection_pullback

/-- The native Clifford Majorana mass generator likewise maps to the pullback
of the finite CAR mass operator used by the BdG/coercivity owner. -/
theorem native_mode_zero_majorana_is_mass_operator_pullback :
    cl55ToStage5 (creation55 0 + annihilation55 0) =
      exteriorToWittStageEquiv.symm
        InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.carMassOperator := by
  apply exteriorToWittStageEquiv.injective
  have h : exteriorToWittStageEquiv
      (cl55ToStage5 (creation55 0 + annihilation55 0)) =
      creation 0 + annihilation 0 := by
    calc
      exteriorToWittStageEquiv
          (cl55ToStage5 (creation55 0 + annihilation55 0)) =
        exteriorToWittStageEquiv
          (cl55ToStage5 (creation55 0) + cl55ToStage5 (annihilation55 0)) := by
            rw [map_add cl55ToStage5]
      _ =
        exteriorToWittStageEquiv (cl55ToStage5 (creation55 0)) +
          exteriorToWittStageEquiv (cl55ToStage5 (annihilation55 0)) :=
            map_add exteriorToWittStageEquiv
              (cl55ToStage5 (creation55 0)) (cl55ToStage5 (annihilation55 0))
      _ = creation 0 + annihilation 0 := by
        rw [exteriorToWitt_creation55, exteriorToWitt_annihilation55]
  simpa [InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.carMassOperator]
    using h

/-- The Clifford Majorana mass has the same calibrated representative in the
UHF inductive colimit. -/
theorem native_mode_zero_majorana_in_UHF_limit :
    ofStage 5 (cl55ToStage5 (creation55 0 + annihilation55 0)) =
      ofStage 5 (exteriorToWittStageEquiv.symm
        InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.carMassOperator) := by
  exact congrArg (ofStage 5) native_mode_zero_majorana_is_mass_operator_pullback

/-- The calibrated native Majorana mass remains an involution after the
finite stage is embedded in the actual UHF inductive colimit. -/
theorem native_mode_zero_majorana_square_eq_one_in_UHF_limit :
    ofStage 5 (cl55ToStage5 (creation55 0 + annihilation55 0)) *
      ofStage 5 (cl55ToStage5 (creation55 0 + annihilation55 0)) = 1 := by
  have hStage :
      cl55ToStage5 (creation55 0 + annihilation55 0) *
        cl55ToStage5 (creation55 0 + annihilation55 0) = 1 := by
    rw [native_mode_zero_majorana_is_mass_operator_pullback]
    apply exteriorToWittStageEquiv.injective
    simpa using
      InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.carMassOperator_square_eq_one
  calc
    ofStage 5 (cl55ToStage5 (creation55 0 + annihilation55 0)) *
        ofStage 5 (cl55ToStage5 (creation55 0 + annihilation55 0)) =
      ofStage 5 (cl55ToStage5 (creation55 0 + annihilation55 0) *
        cl55ToStage5 (creation55 0 + annihilation55 0)) := by rw [map_mul]
    _ = ofStage 5 1 := by rw [hStage]
    _ = 1 := map_one (ofStage 5)

end InfoGeometry.Canonical.Cl55CARRepresentationCalibration

end

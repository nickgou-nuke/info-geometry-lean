/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
import InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading

/-!
# Cl(5,5) generators on the finite CAR–CCR carrier

The Cl(5,5) vacuum-spinor representation and the finite common carrier use
the same exterior creation and contraction operators.  These identities
identify the represented generators themselves, rather than merely comparing
their CAR relations.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteCARCCRCommonCarrier

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge
open InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.Twistor.RealPolynomialCCR

/-- Transporting left multiplication on the concrete vacuum ideal through
the existing ideal-to-spinor equivalence gives the spinor endomorphism used
by the common CAR–CCR carrier. This is the operator-level carrier bridge;
the equivalence acts on endomorphism algebras, not on spinor states. -/
theorem cl55_vacuum_ideal_representation_on_common_carrier (a : Cl55) :
    fermionLift (Fin 5) (Fin 5 → ℝ)
      (((InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealSpinorEquiv).conjAlgEquiv ℝ)
          (InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealLeftAction a)) =
      cl55CommonCarrierRep a := by
  have hSpinor :
      ((InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealSpinorEquiv).conjAlgEquiv ℝ)
          (InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealLeftAction a) =
        cl55SpinorRep a := by
    apply LinearMap.ext
    intro ψ
    change InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealSpinorEquiv
        (InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealLeftAction a
          (InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealSpinorEquiv.symm ψ)) =
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.neutralCliffordRep
        (InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm a) ψ
    rw [InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealLeftAction_intertwines]
    rw [InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge.cl55VacuumIdealSpinorEquiv.apply_symm_apply]
  rw [hSpinor]
  rfl

/-- The positive-null Cl(5,5) generator acts as the same exterior creation
operator used by the common finite CAR–CCR carrier. -/
theorem cl55_annihilation_eq_common_fermionCreate (i : Fin 5) :
    cl55CommonCarrierRep (annihilation55 i) = fermionCreate 5 i := by
  have h := congrArg (fermionLift (Fin 5) (Fin 5 → ℝ))
    (annihilation55_spinor i)
  simpa [cl55CommonCarrierRep, cl55SpinorRep, fermionCreate,
    InfoGeometry.Twistor.RealSupertwistor.fermionCreate,
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.wedge,
    InfoGeometry.Canonical.KahlerAtiyahCartanForms.wedgeOperator,
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.basisVector] using h

/-- The negative-null Cl(5,5) generator acts as the same exterior contraction
operator used by the common finite CAR–CCR carrier. -/
theorem cl55_creation_eq_common_fermionAnnihilate (i : Fin 5) :
    cl55CommonCarrierRep (creation55 i) = fermionAnnihilate (Fin 5) (Fin 5 → ℝ)
      (dualBasisVector i) := by
  have h := congrArg (fermionLift (Fin 5) (Fin 5 → ℝ))
    (creation55_spinor i)
  simpa [cl55CommonCarrierRep, cl55SpinorRep, fermionAnnihilate,
    InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate,
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.contract,
    InfoGeometry.Canonical.KahlerAtiyahCartanForms.contractionOperator,
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.dualBasisVector] using h

/-- Consequently, the Cl(5,5) pair on the common carrier has exactly the
same CAR anticommutator as the canonical exterior-Fock pair. -/
theorem cl55_common_carrier_is_the_finite_fock_CAR (i j : Fin 5) :
    cl55CommonCarrierRep (creation55 j) * cl55CommonCarrierRep (annihilation55 i) +
      cl55CommonCarrierRep (annihilation55 i) * cl55CommonCarrierRep (creation55 j) =
      (if i = j then 1 else 0 : ℝ) •
        (1 : SuperOperator (Fin 5) (Fin 5 → ℝ)) := by
  rw [cl55_creation_eq_common_fermionAnnihilate,
    cl55_annihilation_eq_common_fermionCreate]
  simpa [fermionCreate, InfoGeometry.Twistor.RealSupertwistor.fermionCreate,
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.dualBasisVector,
    InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.basisVector,
    Pi.single_apply, eq_comm] using
    (fermionic_CAR (ι := Fin 5) (E := Fin 5 → ℝ)
      (LinearMap.proj j) (Pi.single i (1 : ℝ)))

/-- The represented positive chiral Cl(5,5) supercharge is precisely the
positive block supercharge already defined on the common CAR–CCR carrier. -/
theorem cl55_QPlus_maps_to_commonCarrierQPlus (i : Fin 5) :
    Matrix.map (cl55QPlus i) cl55CommonCarrierRep = commonCarrierQPlus i := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.map_apply, cl55QPlus, commonCarrierQPlus,
      InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qPlus]

/-- The represented negative chiral Cl(5,5) supercharge is precisely the
negative block supercharge already defined on the common CAR–CCR carrier. -/
theorem cl55_QMinus_maps_to_commonCarrierQMinus (i : Fin 5) :
    Matrix.map (cl55QMinus i) cl55CommonCarrierRep = commonCarrierQMinus i := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.map_apply, cl55QMinus, commonCarrierQMinus,
      InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative.qMinus]

/-- The geometric infinity and origin endpoints are the fourth native CAR
mode, represented on the same polynomial–Fock carrier used by the CCR
operators.  The orientation follows the repository's calibrated convention:
infinity acts by contraction and origin by exterior creation. -/
theorem infinity_origin_endpoints_on_common_carrier :
    cl55CommonCarrierRep infinityClifford55 =
      fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) ∧
    cl55CommonCarrierRep originClifford55 = fermionCreate 5 4 ∧
    cl55CommonCarrierRep infinityClifford55 *
        cl55CommonCarrierRep infinityClifford55 = 0 ∧
    cl55CommonCarrierRep originClifford55 *
        cl55CommonCarrierRep originClifford55 = 0 ∧
    cl55CommonCarrierRep infinityClifford55 *
        cl55CommonCarrierRep originClifford55 +
      cl55CommonCarrierRep originClifford55 *
        cl55CommonCarrierRep infinityClifford55 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [infinityClifford55_eq_creation55]
    exact cl55_creation_eq_common_fermionAnnihilate 4
  · rw [originClifford55_eq_annihilation55]
    exact cl55_annihilation_eq_common_fermionCreate 4
  · rw [infinityClifford55_eq_creation55]
    calc
      cl55CommonCarrierRep (creation55 4) * cl55CommonCarrierRep (creation55 4) =
          cl55CommonCarrierRep (creation55 4 * creation55 4) := by rw [map_mul]
      _ = 0 := by rw [creation55_sq, map_zero]
  · rw [originClifford55_eq_annihilation55]
    calc
      cl55CommonCarrierRep (annihilation55 4) * cl55CommonCarrierRep (annihilation55 4) =
          cl55CommonCarrierRep (annihilation55 4 * annihilation55 4) := by rw [map_mul]
      _ = 0 := by rw [annihilation55_sq, map_zero]
  · rw [infinityClifford55_eq_creation55, originClifford55_eq_annihilation55]
    simpa only [map_mul, map_add, map_one, add_comm] using
      congrArg cl55CommonCarrierRep (annihilation55_creation55_anticommutator 4)

/-- The two complementary projectors cut out by the geometric infinity/origin
pair become the empty and occupied projections of CAR mode `4` on the common
polynomial–Fock operator carrier.  In particular, the orientation is fixed by
the actual representation: `infinity * origin` is the unoccupied projection,
while `origin * infinity` is the occupation operator. -/
theorem infinity_origin_projectors_are_mode_four_occupation_complements :
    cl55CommonCarrierRep infinityProjector55 =
        1 - fermionCreate 5 4 *
          fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) ∧
    cl55CommonCarrierRep originProjector55 =
        fermionCreate 5 4 *
          fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) := by
  rcases infinity_origin_endpoints_on_common_carrier with
    ⟨hInfinity, hOrigin, _, _, hCAR⟩
  have hFockCAR :
      fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) *
          fermionCreate 5 4 +
        fermionCreate 5 4 *
          fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) = 1 := by
    simpa only [hInfinity, hOrigin] using hCAR
  have hInfinityProj : cl55CommonCarrierRep infinityProjector55 =
      fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) *
        fermionCreate 5 4 := by
    rw [infinityProjector55, map_mul, hInfinity, hOrigin]
  have hOriginProj : cl55CommonCarrierRep originProjector55 =
      fermionCreate 5 4 *
        fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) := by
    rw [originProjector55, map_mul, hOrigin, hInfinity]
  have hComplement :
      fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) *
          fermionCreate 5 4 =
        1 - fermionCreate 5 4 *
          fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) := by
    calc
      fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) *
          fermionCreate 5 4 =
        (fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) *
            fermionCreate 5 4 +
          fermionCreate 5 4 *
            fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4)) -
          fermionCreate 5 4 *
            fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) := by
              abel
      _ = 1 - fermionCreate 5 4 *
          fermionAnnihilate (Fin 5) (Fin 5 → ℝ) (LinearMap.proj 4) := by
        rw [hFockCAR]
  exact ⟨by rw [hInfinityProj, hComplement], hOriginProj⟩

/-- Both polynomial CCR generators commute with each geometric endpoint after
transport to the common carrier.  Thus the endpoint CAR pair and bosonic CCR
act as separate sectors of one actual operator module. -/
theorem finiteCCR_generators_commute_with_infinity_origin (i : Fin 5) :
    (bosonLift (Fin 5) (Fin 5 → ℝ) (create i) *
        cl55CommonCarrierRep infinityClifford55 =
      cl55CommonCarrierRep infinityClifford55 *
        bosonLift (Fin 5) (Fin 5 → ℝ) (create i)) ∧
    (bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i) *
        cl55CommonCarrierRep infinityClifford55 =
      cl55CommonCarrierRep infinityClifford55 *
        bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i)) ∧
    (bosonLift (Fin 5) (Fin 5 → ℝ) (create i) *
        cl55CommonCarrierRep originClifford55 =
      cl55CommonCarrierRep originClifford55 *
        bosonLift (Fin 5) (Fin 5 → ℝ) (create i)) ∧
    (bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i) *
        cl55CommonCarrierRep originClifford55 =
      cl55CommonCarrierRep originClifford55 *
        bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [infinityClifford55_eq_creation55]
    exact commonCarrier_boson_cl55_commute (create i) (creation55 4)
  · rw [infinityClifford55_eq_creation55]
    exact commonCarrier_boson_cl55_commute (annihilate i) (creation55 4)
  · rw [originClifford55_eq_annihilation55]
    exact commonCarrier_boson_cl55_commute (create i) (annihilation55 4)
  · rw [originClifford55_eq_annihilation55]
    exact commonCarrier_boson_cl55_commute (annihilate i) (annihilation55 4)

end InfoGeometry.Canonical.FiniteCARCCRCommonCarrier

end

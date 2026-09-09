import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearBdGBogoliubovCAR
import InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel

/-! Verified end-to-end finite CAR--CCR--BdG--Soloviev closure. -/
noncomputable section
namespace InfoGeometry.Physics.NuclearFiveGradeSolovievBdGClosure

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
open InfoGeometry.Physics.SolovievQPNMEigenproblem

theorem common_operator_carrier_closure (D E : NativeZornDerLie) :
    representation InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 *
          representation InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag +
        representation InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag *
          representation InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 = 1 ∧
      phononAnnihilation * phononCreation -
          phononCreation * phononAnnihilation = 1 ∧
      representation pairCreation * phononCreation =
          phononCreation * representation pairCreation ∧
      coefficientLift ((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) =
        coefficientLift (D : NativeZornEnd) * coefficientLift (E : NativeZornEnd) -
          coefficientLift (E : NativeZornEnd) * coefficientLift (D : NativeZornEnd) := by
  have h := five_grade_common_representation_packet D E
  exact h.2.2

theorem projected_soloviev_closure (Eqp omega V C D : ℝ) :
    modelProjection * modelProjection = modelProjection ∧
      modelProjection (modelEmbed ![C, D]) = modelEmbed ![C, D] ∧
      modelProjection (fullHamiltonian Eqp omega V
        (modelProjection (modelEmbed ![C, D]))) =
        modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C, D]) := by
  exact ⟨modelProjection_idempotent,
    modelProjection_modelEmbed _,
    projected_fullHamiltonian_on_model Eqp omega V C D⟩

theorem finite_bdg_soloviev_closure (ξ Δ Eqp omega V C D : ℝ) :
    compressedAction Eqp omega V ![C, D] =
        mulVec (qpnmMatrix Eqp omega V) ![C, D] ∧
      qpnmMatrix Eqp omega V =
        solovievCenter Eqp omega •
          (1 : InfoGeometry.Physics.SolovievQPNMEigenproblem.M2R) +
          bdgBlock (solovievBdGCoordinate omega) V ∧
      bdgBlock ξ Δ * bdgBlock ξ Δ =
        (ξ ^ 2 + Δ ^ 2) •
          (1 : InfoGeometry.Physics.NuclearBdGTwoLevelExact.M2R) := by
  exact ⟨compressedAction_eq_qpnm_mulVec Eqp omega V C D,
    qpnm_eq_center_add_bdg Eqp omega V,
    bdgBlock_sq ξ Δ⟩

end InfoGeometry.Physics.NuclearFiveGradeSolovievBdGClosure

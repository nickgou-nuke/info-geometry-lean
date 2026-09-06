import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearBdGSolovievAffineBridge

/-!
# End-to-end same-carrier nuclear closure

This capstone records the concrete chain on one represented carrier:

* the two-mode CAR commutator Lie algebra acts by a native Lie homomorphism;
* the five adjoint grades are preserved;
* fermionic CAR and phonon CCR coexist and commute;
* a model-space idempotent compresses the represented Hamiltonian to the
  finite Soloviev QPNM block;
* the finite block is a scalar center plus a traceless BdG block;
* the BdG block has the exact square/spectral/particle-hole identities.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure

open Matrix
open InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
open InfoGeometry.Physics.SolovievQPNMEigenproblem

/-- Complete same-carrier theorem packet. -/
theorem nuclear_same_carrier_closure_packet
    (X Y : M4R)
    (D E : NativeZornDerLie)
    (ξ Δ Eqp omega V C₀ C₁ : ℝ)
    (ψ : V2C) :
    commonRepresentationLieHom ⁅X, Y⁆ =
        ⁅commonRepresentationLieHom X,
          commonRepresentationLieHom Y⁆ ∧
      RepresentedHasGrade 2 (representation pairCreation) ∧
      RepresentedHasGrade (-2) (representation pairAnnihilation) ∧
      representation
          InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 *
          representation
            InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag +
        representation
            InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag *
          representation
            InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 = 1 ∧
      phononAnnihilation * phononCreation -
          phononCreation * phononAnnihilation = 1 ∧
      representation pairCreation * phononCreation =
          phononCreation * representation pairCreation ∧
      coefficientLift ((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) =
        coefficientLift (D : NativeZornEnd) *
            coefficientLift (E : NativeZornEnd) -
          coefficientLift (E : NativeZornEnd) *
            coefficientLift (D : NativeZornEnd) ∧
      modelProjection * modelProjection = modelProjection ∧
      modelProjection
          (fullHamiltonian Eqp omega V
            (modelProjection (modelEmbed ![C₀, C₁]))) =
        modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C₀, C₁]) ∧
      qpnmMatrix Eqp omega V =
        solovievCenter Eqp omega •
            (1 : InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.M2R) +
          bdgBlock (solovievBdGCoordinate omega) V ∧
      bdgBlock ξ Δ * bdgBlock ξ Δ =
        (ξ ^ 2 + Δ ^ 2) •
          (1 : InfoGeometry.Physics.NuclearBdGTwoLevelExact.M2R) ∧
      bdgBlock ξ Δ * bdgEigenbasis ξ Δ =
        bdgEigenbasis ξ Δ * bdgSpectrum ξ Δ ∧
      particleHole (particleHole ψ) = -ψ ∧
      particleHole (mulVec (bdgBlockC ξ Δ) ψ) =
        -mulVec (bdgBlockC ξ Δ) (particleHole ψ) := by
  refine ⟨commonRepresentationLieHom.map_lie X Y,
    representation_preserves_grade pairCreation_grade,
    representation_preserves_grade pairAnnihilation_grade,
    represented_mode1_CAR,
    phonon_CCR,
    representation_commutes_phononCreation pairCreation,
    ?_,
    modelProjection_idempotent,
    projected_fullHamiltonian_on_model Eqp omega V C₀ C₁,
    qpnm_eq_center_add_bdg Eqp omega V,
    bdgBlock_sq ξ Δ,
    bdg_eigenbasis_intertwines ξ Δ,
    particleHole_sq ψ,
    particleHole_anticommutes ξ Δ ψ⟩
  change coefficientLift
      ((D : NativeZornEnd) * (E : NativeZornEnd) -
        (E : NativeZornEnd) * (D : NativeZornEnd)) = _
  exact coefficientLift_commutator (D : NativeZornEnd) (E : NativeZornEnd)

end InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure

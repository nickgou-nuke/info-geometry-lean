import InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
import InfoGeometry.Physics.NuclearCARPhononCommonCarrier
import InfoGeometry.Physics.NuclearSolovievCompression
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
import InfoGeometry.Exceptional.FreudenthalSymplecticTKKJacobiObstruction

/-!
# Concrete closure of the nuclear five-grade / CAR / phonon / BdG / Soloviev lane

This capstone separates two facts.

1. The generic Freudenthal bracket candidate still has an explicit mixed
   Jacobi obstruction unless its missing triple identity is established.
2. The concrete nuclear operator realization is already globally closed:
   two-mode CAR matrices give a genuine five-grading and global Jacobi; a
   common infinite occupation carrier gives exact CAR and CCR; compression
   yields the finite Soloviev matrix; and every Soloviev block is an affine
   scalar shift of a traceless BdG block.

The second statement is a complete finite/algebraic model.  It does not erase
or assume away the first, more general, exceptional-algebra frontier.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeSolovievBdGClosure

open Matrix
open InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearCARPhononCommonCarrier
open InfoGeometry.Physics.NuclearSolovievCompression
open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
open InfoGeometry.Physics.SolovievQPNMEigenproblem

/-- Concrete global Lie/five-grade packet. -/
theorem concrete_five_grade_global_closure
    (X Y Z : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R) :
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 ∧
      HasGrade 2 pairCreation ∧
      HasGrade 1
        InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag ∧
      HasGrade 1
        InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag ∧
      HasGrade (-1)
        InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 ∧
      HasGrade (-1)
        InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2 ∧
      HasGrade (-2) pairAnnihilation ∧
      comm pairCreation pairAnnihilation = gradingOperator := by
  exact ⟨comm_jacobi X Y Z,
    pairCreation_grade,
    a1Dag_grade,
    a2Dag_grade,
    a1_grade,
    a2_grade,
    pairAnnihilation_grade,
    pair_extreme_bracket⟩

/-- Common-carrier exact CAR/CCR and derivation symmetry. -/
theorem common_operator_carrier_closure
    (D E : NativeZornDerLie) :
    qpAnnihilation * qpCreation + qpCreation * qpAnnihilation = 1 ∧
      phononAnnihilation * phononCreation -
          phononCreation * phononAnnihilation = 1 ∧
      qpCreation * phononCreation = phononCreation * qpCreation ∧
      coefficientLift ((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) =
        coefficientLift (D : NativeZornEnd) *
            coefficientLift (E : NativeZornEnd) -
          coefficientLift (E : NativeZornEnd) *
            coefficientLift (D : NativeZornEnd) := by
  have h := common_car_phonon_packet D E
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The full operator compression and finite BdG/Soloviev spectral relation. -/
theorem finite_bdg_soloviev_closure
    (ξ Δ Eqp omega V C D : ℝ)
    (ψ : InfoGeometry.Physics.NuclearBdGTwoLevelExact.V2C) :
    modelReadout (modelEmbed ![C, D]) = ![C, D] ∧
      compressedAction Eqp omega V ![C, D] =
        mulVec (qpnmMatrix Eqp omega V) ![C, D] ∧
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
      particleHole
          (mulVec (bdgBlockC ξ Δ) ψ) =
        -mulVec (bdgBlockC ξ Δ) (particleHole ψ) := by
  exact ⟨modelReadout_modelEmbed _,
    compressedAction_eq_qpnm_mulVec Eqp omega V C D,
    qpnm_eq_center_add_bdg Eqp omega V,
    bdgBlock_sq ξ Δ,
    bdg_eigenbasis_intertwines ξ Δ,
    particleHole_sq ψ,
    particleHole_anticommutes ξ Δ ψ⟩

/-- End-to-end concrete theorem packet. -/
theorem nuclear_five_grade_car_phonon_bdg_soloviev_packet
    (X Y Z : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R)
    (D₁ D₂ : NativeZornDerLie)
    (ξ Δ omega V C₀ C₁ : ℝ)
    (ψ : InfoGeometry.Physics.NuclearBdGTwoLevelExact.V2C) :
    comm X (comm Y Z) + comm Y (comm Z X) + comm Z (comm X Y) = 0 ∧
      HasGrade 2 pairCreation ∧
      qpAnnihilation * qpCreation + qpCreation * qpAnnihilation = 1 ∧
      phononAnnihilation * phononCreation -
          phononCreation * phononAnnihilation = 1 ∧
      modelReadout
          (bdgSolovievHamiltonian ξ Δ omega V
            (modelEmbed ![C₀, C₁])) =
        mulVec (bdgSolovievBlock ξ Δ omega V) ![C₀, C₁] ∧
      bdgSolovievBlock ξ Δ omega V =
        solovievCenter (bdgEnergy ξ Δ) omega •
            (1 : InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.M2R) +
          bdgBlock (solovievBdGCoordinate omega) V ∧
      particleHole (particleHole ψ) = -ψ ∧
      coefficientLift
          ((⁅D₁, D₂⁆ : NativeZornDerLie) : NativeZornEnd) =
        coefficientLift (D₁ : NativeZornEnd) *
            coefficientLift (D₂ : NativeZornEnd) -
          coefficientLift (D₂ : NativeZornEnd) *
            coefficientLift (D₁ : NativeZornEnd) := by
  refine ⟨comm_jacobi X Y Z,
    pairCreation_grade,
    qp_CAR,
    phonon_CCR,
    bdgSoloviev_compression ξ Δ omega V C₀ C₁,
    bdgSolovievBlock_affine ξ Δ omega V,
    particleHole_sq ψ,
    ?_⟩
  have h := common_car_phonon_packet D₁ D₂
  exact h.2.2.2.1

end InfoGeometry.Physics.NuclearFiveGradeSolovievBdGClosure

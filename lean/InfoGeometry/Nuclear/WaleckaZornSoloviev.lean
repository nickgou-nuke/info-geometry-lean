import InfoGeometry.Nuclear.WaleckaZornBdG
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
import InfoGeometry.Canonical.KantorPeirceFiveGrading

namespace InfoGeometry.Nuclear.WaleckaZornSoloviev

open InfoGeometry.Nuclear.NambuGorkov
open InfoGeometry.Nuclear.WaleckaZornBdG
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.SolovievQPNMEigenproblem

noncomputable section

def coefficientHamiltonian (state : NambuGorkovCarrier ℝ) : Operator :=
  coefficientLift (regularHamiltonian state)

theorem coefficientHamiltonian_square (state : NambuGorkovCarrier ℝ) :
    coefficientHamiltonian state * coefficientHamiltonian state =
      (bogoliubovEnergy state) ^ 2 • (1 : Operator) := by
  apply LinearMap.ext
  intro vector
  funext occupation slot
  exact LinearMap.congr_fun (regularHamiltonian_square state) (vector occupation slot)

theorem coefficientHamiltonian_grade_zero (state : NambuGorkovCarrier ℝ) :
    RepresentedHasGrade 0 (coefficientHamiltonian state) := by
  unfold RepresentedHasGrade coefficientHamiltonian
  rw [← coefficientLift_commutes_representation, sub_self, zero_smul]

theorem coefficientHamiltonian_preserves_grade (state : NambuGorkovCarrier ℝ)
    (grade : ℤ) (channel : Operator) (channel_grade : RepresentedHasGrade grade channel) :
    RepresentedHasGrade grade (coefficientHamiltonian state * channel) := by
  have zero_component : InfoGeometry.Canonical.IsCommutatorComponent
      (representation InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator)
      (coefficientHamiltonian state) 0 := coefficientHamiltonian_grade_zero state
  have channel_component : InfoGeometry.Canonical.IsCommutatorComponent
      (representation InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator)
      channel (grade : ℝ) := channel_grade
  simpa only [zero_add] using
    InfoGeometry.Canonical.commutatorAction_product_component zero_component channel_component

theorem coefficientHamiltonian_commutes_phonons (state : NambuGorkovCarrier ℝ) :
    coefficientHamiltonian state * phononCreation =
        phononCreation * coefficientHamiltonian state ∧
      coefficientHamiltonian state * phononAnnihilation =
        phononAnnihilation * coefficientHamiltonian state :=
  coefficientLift_commutes_phonons (regularHamiltonian state)

def meanFieldSolovievHamiltonian
    (bareMass scalarCoupling scalarField : ℝ)
    (pairing : InfoGeometry.Algebra.Vec3 ℝ) (phononEnergy mixing : ℝ) : Operator :=
  fullHamiltonian
    (bogoliubovEnergy (meanFieldState bareMass scalarCoupling scalarField pairing))
    phononEnergy mixing

theorem meanFieldSoloviev_compression
    (bareMass scalarCoupling scalarField : ℝ)
    (pairing : InfoGeometry.Algebra.Vec3 ℝ)
    (phononEnergy mixing amplitudeZero amplitudeOne : ℝ) :
    modelProjection
        (meanFieldSolovievHamiltonian bareMass scalarCoupling scalarField pairing
          phononEnergy mixing (modelProjection (modelEmbed ![amplitudeZero, amplitudeOne]))) =
      modelEmbed (Matrix.mulVec
        (qpnmMatrix
          (bogoliubovEnergy (meanFieldState bareMass scalarCoupling scalarField pairing))
          phononEnergy mixing) ![amplitudeZero, amplitudeOne]) :=
  projected_fullHamiltonian_on_model _ _ _ _ _

end

end InfoGeometry.Nuclear.WaleckaZornSoloviev

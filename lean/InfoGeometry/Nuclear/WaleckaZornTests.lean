import InfoGeometry.Nuclear.WaleckaZornSoloviev

namespace InfoGeometry.Nuclear.WaleckaZornTests

open InfoGeometry.Algebra
open InfoGeometry.Nuclear.NambuGorkov
open InfoGeometry.Nuclear.WaleckaZornBdG
open InfoGeometry.Nuclear.WaleckaZornSoloviev

noncomputable section

example : effectiveMass 3 1 2 = 1 := by
  norm_num [effectiveMass]

example : effectiveMass 1 1 2 < 0 := by
  norm_num [effectiveMass]

example : pairingMassRatio (meanFieldState 1 1 1 ![1, 0, 0]) = 0 := by
  norm_num [pairingMassRatio, meanFieldState, effectiveMass]

example : ZornVectorMatrix.mul
    (nativeHamiltonian ⟨3, ![4, 0, 0]⟩)
    (nativeHamiltonian ⟨3, ![4, 0, 0]⟩) =
      (25 : ℝ) • ZornVectorMatrix.one := by
  rw [nativeHamiltonian_square, bogoliubovEnergy_sq, nambu_gorkov_zornNorm]
  norm_num [Vec3.dot]

example : regularHamiltonian (meanFieldState 1 1 1 ![1, 0, 0]) *
    regularHamiltonian (meanFieldState 1 1 1 ![1, 0, 0]) = 1 := by
  simpa [Vec3.dot] using meanField_massless_square 1 1 1 ![1, 0, 0] (by norm_num)

example : pairingMassRatio ⟨3, ![1, 0, 0]⟩ <
    pairingMassRatio (meanFieldState 3 1 2 ![1, 0, 0]) := by
  apply meanField_pairingMassRatio_increases <;>
    norm_num [effectiveMass, Vec3.dot]

example (state : NambuGorkovCarrier ℝ) :
    InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation.RepresentedHasGrade 2
      (coefficientHamiltonian state *
        InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation.representation
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation) := by
  apply coefficientHamiltonian_preserves_grade
  exact InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation.representation_preserves_grade
    InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation_grade

#print axioms nativeHamiltonian_square
#print axioms regularHamiltonian_square
#print axioms meanField_massless_square
#print axioms meanField_pairingMassRatio_increases
#print axioms coefficientHamiltonian_square
#print axioms coefficientHamiltonian_grade_zero
#print axioms coefficientHamiltonian_preserves_grade
#print axioms coefficientHamiltonian_commutes_phonons
#print axioms meanFieldSoloviev_compression
#print axioms InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication_not_multiplicative

end

end InfoGeometry.Nuclear.WaleckaZornTests

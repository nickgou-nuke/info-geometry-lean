import InfoGeometry.Physics.SolovievTwoModePhonon

noncomputable section

namespace InfoGeometry.Physics.SolovievPhononCorrectionsTests

open NuclearTwoModeCARFiveGrade SolovievPhononCorrections SolovievTwoModePhonon
open NuclearQuasiparticleCAR.QuasiparticleCAR

example :
    (((3 / 5 : ℝ) • twoModeCAR.a 0 + (4 / 5 : ℝ) • twoModeCAR.adag 1) *
        ((3 / 5 : ℝ) • twoModeCAR.adag 0 + (4 / 5 : ℝ) • twoModeCAR.a 1) +
      ((3 / 5 : ℝ) • twoModeCAR.adag 0 + (4 / 5 : ℝ) • twoModeCAR.a 1) *
        ((3 / 5 : ℝ) • twoModeCAR.a 0 + (4 / 5 : ℝ) • twoModeCAR.adag 1)) = 1 := by
  rw [twoModeCAR.bogoliubov_anticommutator]
  have normalized : (3 / 5 : ℝ) ^ 2 + (4 / 5 : ℝ) ^ 2 = 1 := by norm_num
  rw [normalized]
  exact one_smul ℝ (1 : Op)

example : Complex.normSq (circularAmplitude 2 1) = 1 := by
  rw [circularAmplitude_normSq 2 1 (by norm_num)]
  norm_num

example : Complex.normSq (circularAmplitude 2 (-1)) = 1 := by
  rw [circularAmplitude_normSq 2 (-1) (by norm_num)]
  norm_num

example :
    comm (phononAnnihilation twoModeCAR 0 1 (5 / 3) (4 / 3))
        (phononCreation twoModeCAR 0 1 (5 / 3) (4 / 3))
        (![1, 0, 0, 0] : Fock4) = (![1, 0, 0, 0] : Fock4) := by
  apply normalized_commutator_on_vacuum
  norm_num [Complex.normSq_apply]

example :
    comm (phononAnnihilation twoModeCAR 0 1 (5 / 3) (4 / 3))
        (phononCreation twoModeCAR 0 1 (5 / 3) (4 / 3)) ≠ 1 := by
  apply normalized_commutator_ne_identity
  norm_num [Complex.normSq_apply]

example :
    comm
        (phononAnnihilation twoModeCAR 0 1
          (circularAmplitude 2 1) (circularAmplitude 0 (-1)))
        (phononCreation twoModeCAR 0 1
          (circularAmplitude 2 1) (circularAmplitude 0 (-1))) = -gradeCartan := by
  rw [circular_phonon_commutator twoModeCAR 0 1 (by decide) 2 0 1 (by norm_num)]
  norm_num
  change 1 - numberOne - numberTwo = -(numberOne + numberTwo - 1)
  abel

#print axioms pair_commutator_normal_order
#print axioms pair_commutator_same
#print axioms bogoliubov_anticommutator
#print axioms pair_mode_commutator
#print axioms normalized_pair_mode_correction
#print axioms phonon_commutator
#print axioms normalized_phonon_defect
#print axioms circularAmplitude_normSq
#print axioms circular_phonon_commutator
#print axioms normalized_phonon_on_vacuum
#print axioms ProofDependency.correction_prerequisites
#print axioms ProofDependency.circular_and_vacuum_incomparable
#print axioms twoModeCAR
#print axioms phononCreation_eq_pair_components
#print axioms phonon_commutator_eq_cartan
#print axioms normalized_commutator_on_occupied
#print axioms normalized_commutator_ne_identity
#print axioms normalized_commutator_on_vacuum
#print axioms pair_component_grades

end InfoGeometry.Physics.SolovievPhononCorrectionsTests

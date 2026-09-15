import InfoGeometry.Physics.SolovievPhononCorrections
import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

noncomputable section

namespace InfoGeometry.Physics.SolovievTwoModePhonon

open NuclearTwoModeCARFiveGrade SolovievPhononCorrections
open NuclearQuasiparticleCAR
open NuclearQuasiparticleCAR.QuasiparticleCAR

def twoModeCAR : QuasiparticleCAR (Fin 2) Op where
  a := ![annihilationOne, annihilationTwo]
  adag := ![creationOne, creationTwo]
  anticomm_a_a := by
    intro first second
    fin_cases first <;> fin_cases second
    · simp
    · simpa using CAR_annihilation_cross
    · simpa [add_comm] using CAR_annihilation_cross
    · simp
  anticomm_adag_adag := by
    intro first second
    fin_cases first <;> fin_cases second
    · simp
    · simpa using CAR_creation_cross
    · simpa [add_comm] using CAR_creation_cross
    · simp
  anticomm_a_adag := by
    intro first second
    fin_cases first <;> fin_cases second
    · simpa using CAR_one
    · simpa using CAR_one_two_mixed
    · simpa using CAR_two_one_mixed
    · simpa using CAR_two

theorem phononCreation_eq_pair_components (forward backward : ℂ) :
    phononCreation twoModeCAR 0 1 forward backward =
      forward • pairCreation - backward • pairAnnihilation := rfl

theorem phonon_commutator_eq_cartan (forward backward : ℂ) :
    comm (phononAnnihilation twoModeCAR 0 1 forward backward)
        (phononCreation twoModeCAR 0 1 forward backward) =
      -((Complex.normSq forward - Complex.normSq backward : ℝ) : ℂ) •
        gradeCartan := by
  rw [phonon_commutator twoModeCAR 0 1 (by decide)]
  have occupation : 1 - twoModeCAR.numberOp 0 - twoModeCAR.numberOp 1 =
      -gradeCartan := by
    change 1 - numberOne - numberTwo = -(numberOne + numberTwo - 1)
    abel
  rw [occupation]
  module

theorem normalized_commutator_on_occupied (forward backward : ℂ)
    (normalized : Complex.normSq forward - Complex.normSq backward = 1) :
    comm (phononAnnihilation twoModeCAR 0 1 forward backward)
        (phononCreation twoModeCAR 0 1 forward backward)
        (![0, 0, 0, 1] : Fock4) = -(![0, 0, 0, 1] : Fock4) := by
  rw [phonon_commutator_eq_cartan, normalized]
  ext coordinate
  fin_cases coordinate <;> simp [smul_eq_mul]

theorem normalized_commutator_ne_identity (forward backward : ℂ)
    (normalized : Complex.normSq forward - Complex.normSq backward = 1) :
    comm (phononAnnihilation twoModeCAR 0 1 forward backward)
        (phononCreation twoModeCAR 0 1 forward backward) ≠ 1 := by
  intro identity
  have occupied := normalized_commutator_on_occupied forward backward normalized
  rw [identity] at occupied
  have component := congrArg (fun state : Fock4 => state 3) occupied
  change (1 : ℂ) = -1 at component
  norm_num at component

theorem normalized_commutator_on_vacuum (forward backward : ℂ)
    (normalized : Complex.normSq forward - Complex.normSq backward = 1) :
    comm (phononAnnihilation twoModeCAR 0 1 forward backward)
        (phononCreation twoModeCAR 0 1 forward backward)
        (![1, 0, 0, 0] : Fock4) = (![1, 0, 0, 0] : Fock4) := by
  apply normalized_phonon_on_vacuum twoModeCAR 0 1 (by decide)
    forward backward normalized
  · ext coordinate
    fin_cases coordinate <;> simp [twoModeCAR]
  · ext coordinate
    fin_cases coordinate <;> simp [twoModeCAR]

theorem pair_component_grades :
    HasGrade 2 pairCreation ∧ HasGrade (-2) pairAnnihilation :=
  ⟨grade_pairCreation, grade_pairAnnihilation⟩

end InfoGeometry.Physics.SolovievTwoModePhonon

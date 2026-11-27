/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

theorem phononAnnihilation_eq_pair_components (forward backward : ℂ) :
    phononAnnihilation twoModeCAR 0 1 forward backward =
      starRingEnd ℂ forward • pairAnnihilation -
        starRingEnd ℂ backward • pairCreation := rfl

/-- The Tamm–Dancoff forward phonon lies in the grade `+2` pair-creation
sector of the concrete two-mode CAR grading. -/
theorem tda_phonon_creation_grade (forward : ℂ) :
    HasGrade 2 (phononCreation twoModeCAR 0 1 forward 0) := by
  rw [phononCreation_eq_pair_components]
  simp only [zero_smul, sub_zero]
  change commutator gradeCartan (forward • pairCreation) =
    (2 : ℂ) • (forward • pairCreation)
  have hlinear : commutator gradeCartan (forward • pairCreation) =
      forward • commutator gradeCartan pairCreation := by
    simp [NuclearTwoModeCARFiveGrade.commutator,
      smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [hlinear]
  have hgrade : commutator gradeCartan pairCreation =
      (2 : ℂ) • pairCreation := by
    exact grade_pairCreation
  rw [hgrade]
  module

/-- The reverse Tamm–Dancoff phonon lies in the grade `-2`
pair-annihilation sector; the two orientations retain their opposite grades. -/
theorem tda_phonon_annihilation_grade (forward : ℂ) :
    HasGrade (-2) (phononAnnihilation twoModeCAR 0 1 forward 0) := by
  rw [phononAnnihilation_eq_pair_components]
  simp only [map_zero, zero_smul, sub_zero]
  unfold HasGrade
  have hlinear : commutator gradeCartan
      ((starRingEnd ℂ forward) • pairAnnihilation) =
      (starRingEnd ℂ forward) •
        commutator gradeCartan pairAnnihilation := by
    simp [NuclearTwoModeCARFiveGrade.commutator,
      smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [hlinear]
  have hgrade : commutator gradeCartan pairAnnihilation =
      (-2 : ℂ) • pairAnnihilation := by
    simpa [HasGrade] using (grade_pairAnnihilation :
      HasGrade (-2) NuclearTwoModeCARFiveGrade.pairAnnihilation)
  rw [hgrade]
  simp [smul_smul, mul_comm]

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

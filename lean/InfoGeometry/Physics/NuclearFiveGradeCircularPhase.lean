import InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation
import InfoGeometry.Physics.NuclearBdGSolovievCompression

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeCircularPhase

open NuclearTwoModeCARFiveGrade NuclearFiveGradeGeneratorRepresentation
open NuclearBdGSolovievCompression

def quarterTurn : Op where
  toFun state := ![-Complex.I * state 0, state 1, state 2, Complex.I * state 3]
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp <;> ring
  map_smul' scalar state := by
    ext coordinate
    fin_cases coordinate <;> simp <;> ring

theorem quarterTurn_cartan_polynomial :
    quarterTurn = 1 - gradeCartan * gradeCartan + Complex.I • gradeCartan := by
  apply LinearMap.ext
  intro state
  ext coordinate
  fin_cases coordinate <;>
    simp [quarterTurn, Module.End.mul_apply, smul_eq_mul,
      Matrix.vecHead, Matrix.vecTail]

theorem quarterTurn_fourth_power : quarterTurn ^ 4 = 1 := by
  apply LinearMap.ext
  intro state
  ext coordinate
  fin_cases coordinate <;>
    simp [pow_succ, quarterTurn, Module.End.mul_apply, ← mul_assoc]

def circularCharacter : Generator → ℂ
  | .pairAnnihilation | .pairCreation => -1
  | .annihilationOne | .annihilationTwo => -Complex.I
  | .cartan => 1
  | .creationOne | .creationTwo => Complex.I

theorem circularCharacter_eq_grade_phase (generator : Generator) :
    circularCharacter generator = Complex.I ^ degree generator := by
  cases generator <;> simp only [circularCharacter, degree] <;>
    norm_num [zpow_neg, zpow_ofNat, Complex.inv_I, Complex.I_sq]

theorem generator_quarterTurn_covariance (generator : Generator) :
    quarterTurn * represent generator =
      circularCharacter generator • (represent generator * quarterTurn) := by
  cases generator <;> apply LinearMap.ext <;> intro state <;>
    ext coordinate <;> fin_cases coordinate <;>
    simp [quarterTurn, circularCharacter, represent, Module.End.mul_apply,
      smul_eq_mul, ← mul_assoc]

theorem fullSoloviev_quarterTurn_covariance (energy phonon coupling : ℂ) :
    quarterTurn * fullCenteredSoloviev energy phonon coupling =
      fullCenteredSoloviev energy phonon (-coupling) * quarterTurn := by
  apply LinearMap.ext
  intro state
  ext coordinate
  fin_cases coordinate <;>
    simp [fullCenteredSoloviev, fullBdG, quarterTurn, Module.End.mul_apply,
      smul_eq_mul, Matrix.vecHead, Matrix.vecTail] <;> ring

end InfoGeometry.Physics.NuclearFiveGradeCircularPhase

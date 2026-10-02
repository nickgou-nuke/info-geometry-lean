import InfoGeometry.Physics.MengChPSelectionRules
import InfoGeometry.Physics.NuclearFiveGradeCircularPhase
import InfoGeometry.Physics.MengCircularOperatorZorn

noncomputable section

namespace InfoGeometry.Physics.MengChPTranslationTests

open MengChPSelectionRules NuclearFiveGradeCircularPhase MengCircularOperatorZorn

def signOperator : Module.End ℂ (Fin 2 → ℂ) where
  toFun state := ![state 0, -state 1]
  map_add' first second := by ext coordinate; fin_cases coordinate <;> simp [add_comm]
  map_smul' scalar state := by ext coordinate; fin_cases coordinate <;> simp

def flipOperator : Module.End ℂ (Fin 2 → ℂ) where
  toFun state := ![state 1, state 0]
  map_add' first second := by ext coordinate; fin_cases coordinate <;> simp
  map_smul' scalar state := by ext coordinate; fin_cases coordinate <;> simp

theorem flip_covariance :
    signOperator * flipOperator = (-1 : ℂ) • (flipOperator * signOperator) := by
  apply LinearMap.ext
  intro state
  ext coordinate
  fin_cases coordinate <;> simp [signOperator, flipOperator, Module.End.mul_apply]

theorem same_sign_forbidden :
    (LinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →ₗ[ℂ] ℂ)
      (flipOperator ![1, 0]) = 0 := by
  apply matrix_element_selection signOperator flipOperator (LinearMap.proj 0)
    ![1, 0] 1 1 (-1)
  · simp [signOperator]
  · intro state; simp [signOperator]
  · exact flip_covariance
  · norm_num

theorem opposite_sign_nonzero : flipOperator ![1, 0] 1 = 1 := rfl

example : quarterTurn ^ 4 = 1 := quarterTurn_fourth_power

example : circularCharacter .creationOne = Complex.I := rfl

example : circularCharacter .pairCreation = -1 := rfl

def operatorImaginary : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, -Complex.I]

theorem operatorImaginary_sq : operatorImaginary * operatorImaginary = -1 := by
  ext row col
  fin_cases row <;> fin_cases col <;>
    simp [operatorImaginary, Matrix.mul_apply, Fin.sum_univ_two]

example (first second : OperatorZornMatrix (Matrix (Fin 2) (Fin 2) ℂ)) :
    circularReadout operatorImaginary (first * second) =
      circularReadout operatorImaginary first * circularReadout operatorImaginary second :=
  circularReadout_mul operatorImaginary operatorImaginary_sq first second

example (energy phonon coupling spectral : ℂ) :
    Matrix.det (OperatorZornMatrix.toMatrix (circularSoloviev energy phonon coupling) -
      spectral • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        (energy - spectral) * (energy + phonon - spectral) - coupling ^ 2 :=
  circularSoloviev_characteristic energy phonon coupling spectral

end InfoGeometry.Physics.MengChPTranslationTests

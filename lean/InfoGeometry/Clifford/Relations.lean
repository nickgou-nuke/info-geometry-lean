import InfoGeometry.Clifford.Grading
import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dilation operator extracted from the commutator `[J, ε]`. -/
noncomputable def dilationOperator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E))

theorem clmComm_modularJ_spectralEpsilon :
    clmComm (modularJ (E := E)) (spectralEpsilon (E := E))
      = (2 : ℝ) • complexI (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

theorem dilationOperator_eq_complexI :
    dilationOperator (E := E) = complexI (E := E) := by
  rw [dilationOperator, clmComm_modularJ_spectralEpsilon]
  simp [smul_smul]

/-- Algebraic closure relation `[I, J] = -2 ε`. -/
theorem clmComm_complexI_modularJ :
    clmComm (complexI (E := E)) (modularJ (E := E))
      = (-2 : ℝ) • spectralEpsilon (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

/-- Algebraic closure relation `[I, ε] = 2 J`. -/
theorem clmComm_complexI_spectralEpsilon :
    clmComm (complexI (E := E)) (spectralEpsilon (E := E))
      = (2 : ℝ) • modularJ (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

end KreinClifford

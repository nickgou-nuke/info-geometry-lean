import InfoGeometry.Krein.Grading

namespace InfoGeometry.Krein

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def dilationOperator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E))

theorem clmComm_modularJ_spectralEpsilon :
    clmComm (modularJ (E := E)) (spectralEpsilon (E := E)) = (2 : ℝ) • complexI (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

@[simp] theorem dilationOperator_eq_complexI : dilationOperator (E := E) = complexI (E := E) := by
  rw [dilationOperator, clmComm_modularJ_spectralEpsilon]
  simp [smul_smul]

theorem clmComm_complexI_modularJ :
    clmComm (complexI (E := E)) (modularJ (E := E)) = (-2 : ℝ) • spectralEpsilon (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

theorem clmComm_complexI_spectralEpsilon :
    clmComm (complexI (E := E)) (spectralEpsilon (E := E)) = (2 : ℝ) • modularJ (E := E) := by
  ext v <;> simp [clmComm, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

noncomputable def modularJHalf : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • modularJ (E := E)
noncomputable def spectralEpsilonHalf : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • spectralEpsilon (E := E)
noncomputable def complexIHalf : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • complexI (E := E)

lemma clmComm_smul (a b : ℝ) (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm (a • A) (b • B) = (a * b) • clmComm A B := by
  ext v <;> simp [clmComm, smul_sub, smul_smul, mul_comm]

theorem clmComm_modularJHalf_spectralEpsilonHalf :
    clmComm (modularJHalf (E := E)) (spectralEpsilonHalf (E := E)) = complexIHalf (E := E) := by
  rw [modularJHalf, spectralEpsilonHalf, complexIHalf, clmComm_smul, clmComm_modularJ_spectralEpsilon]
  simp [smul_smul]

end InfoGeometry.Krein

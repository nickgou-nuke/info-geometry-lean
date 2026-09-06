import InfoGeometry.Clifford.Grading

section KreinClifford

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

attribute [simp] dilationOperator_eq_complexI

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

/-- Half-scaled `J` generator. -/
noncomputable def modularJHalf : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • modularJ (E := E)

/-- Half-scaled `ε` generator. -/
noncomputable def spectralEpsilonHalf : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • spectralEpsilon (E := E)

/-- Half-scaled `I` generator. -/
noncomputable def complexIHalf : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • complexI (E := E)

lemma clmComm_smul
    (a b : ℝ) (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm (a • A) (b • B) = (a * b) • clmComm A B := by
  ext v <;> simp [clmComm, smul_sub, smul_smul, mul_comm]

/-- Normalized commutator relation `[J', ε'] = I'`. -/
theorem clmComm_modularJHalf_spectralEpsilonHalf :
    clmComm (modularJHalf (E := E)) (spectralEpsilonHalf (E := E))
      = complexIHalf (E := E) := by
  rw [modularJHalf, spectralEpsilonHalf, complexIHalf]
  rw [clmComm_smul (E := E) ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) (modularJ (E := E)) (spectralEpsilon (E := E))]
  rw [clmComm_modularJ_spectralEpsilon (E := E)]
  simp [smul_smul]

/-- Normalized commutator relation `[I', J'] = -ε'`. -/
theorem clmComm_complexIHalf_modularJHalf :
    clmComm (complexIHalf (E := E)) (modularJHalf (E := E))
      = -spectralEpsilonHalf (E := E) := by
  rw [complexIHalf, modularJHalf, spectralEpsilonHalf]
  rw [clmComm_smul (E := E) ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) (complexI (E := E)) (modularJ (E := E))]
  rw [clmComm_complexI_modularJ (E := E)]
  calc
    (((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • ((-2 : ℝ) • spectralEpsilon (E := E))
          : DoubledSpace E →L[ℝ] DoubledSpace E)
        = ((((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) * (-2 : ℝ)) • spectralEpsilon (E := E)) := by
            simp [smul_smul]
    _ = (-((2 : ℝ)⁻¹) : ℝ) • spectralEpsilon (E := E) := by
          norm_num
    _ = -(((2 : ℝ)⁻¹) • spectralEpsilon (E := E)) := by
          exact (neg_smul ((2 : ℝ)⁻¹) (spectralEpsilon (E := E)))

/-- Normalized commutator relation `[I', ε'] = J'`. -/
theorem clmComm_complexIHalf_spectralEpsilonHalf :
    clmComm (complexIHalf (E := E)) (spectralEpsilonHalf (E := E))
      = modularJHalf (E := E) := by
  rw [complexIHalf, spectralEpsilonHalf, modularJHalf]
  rw [clmComm_smul (E := E) ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) (complexI (E := E)) (spectralEpsilon (E := E))]
  rw [clmComm_complexI_spectralEpsilon (E := E)]
  simp [smul_smul]

end KreinClifford

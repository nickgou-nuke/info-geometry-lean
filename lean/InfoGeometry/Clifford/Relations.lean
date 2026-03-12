import InfoGeometry.Clifford.Grading

set_option linter.unusedSectionVars false

namespace InfoGeometry.Krein

section KreinClifford

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Dilation operator extracted from the commutator `[J, ε]`. -/
noncomputable def dilationOperator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • clmComm (modular_j (E := E)) (spectral_epsilon (E := E))

theorem clmComm_modular_j_spectral_epsilon :
    clmComm (modular_j (E := E)) (spectral_epsilon (E := E))
      = (2 : ℝ) • complex_i (E := E) := by
  ext v <;> simp [clmComm, complex_i, modular_j, spectral_epsilon, two_smul, sub_eq_add_neg]

theorem dilationOperator_eq_complex_i :
    dilationOperator (E := E) = complex_i (E := E) := by
  rw [dilationOperator, clmComm_modular_j_spectral_epsilon]
  simp [smul_smul]

attribute [simp] dilationOperator_eq_complex_i

/-- Algebraic closure relation `[I, J] = -2 ε`. -/
theorem clmComm_complex_i_modular_j :
    clmComm (complex_i (E := E)) (modular_j (E := E))
      = (-2 : ℝ) • spectral_epsilon (E := E) := by
  ext v <;> simp [clmComm, complex_i, modular_j, spectral_epsilon, two_smul, sub_eq_add_neg]

/-- Algebraic closure relation `[I, ε] = 2 J`. -/
theorem clmComm_complex_i_spectral_epsilon :
    clmComm (complex_i (E := E)) (spectral_epsilon (E := E))
      = (2 : ℝ) • modular_j (E := E) := by
  ext v <;> simp [clmComm, complex_i, modular_j, spectral_epsilon, two_smul, sub_eq_add_neg]

/-- Half-scaled `J` generator. -/
noncomputable def modular_jHalf : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • modular_j (E := E)

/-- Half-scaled `ε` generator. -/
noncomputable def spectral_epsilonHalf : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • spectral_epsilon (E := E)

/-- Half-scaled `I` generator. -/
noncomputable def complex_iHalf : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • complex_i (E := E)

lemma clmComm_smul
    (a b : ℝ) (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm (a • A) (b • B) = (a * b) • clmComm A B := by
  ext v <;> simp [clmComm, smul_sub, smul_smul, mul_comm]

/-- Normalized commutator relation `[J', ε'] = I'`. -/
theorem clmComm_modular_jHalf_spectral_epsilonHalf :
    clmComm (modular_jHalf (E := E)) (spectral_epsilonHalf (E := E))
      = complex_iHalf (E := E) := by
  rw [modular_jHalf, spectral_epsilonHalf, complex_iHalf]
  rw [clmComm_smul (E := E) ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹)
        (modular_j (E := E)) (spectral_epsilon (E := E))]
  rw [clmComm_modular_j_spectral_epsilon (E := E)]
  simp [smul_smul]

/-- Normalized commutator relation `[I', J'] = -ε'`. -/
theorem clmComm_complex_iHalf_modular_jHalf :
    clmComm (complex_iHalf (E := E)) (modular_jHalf (E := E))
      = -spectral_epsilonHalf (E := E) := by
  rw [complex_iHalf, modular_jHalf, spectral_epsilonHalf]
  rw [clmComm_smul (E := E) ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹)
        (complex_i (E := E)) (modular_j (E := E))]
  rw [clmComm_complex_i_modular_j (E := E)]
  calc
    (((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • ((-2 : ℝ) • spectral_epsilon (E := E))
          : DoubledSpace E →L[ℝ] DoubledSpace E)
        = ((((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) * (-2 : ℝ)) • spectral_epsilon (E := E)) := by
            simp [smul_smul]
    _ = (-((2 : ℝ)⁻¹) : ℝ) • spectral_epsilon (E := E) := by
          norm_num
    _ = -(((2 : ℝ)⁻¹) • spectral_epsilon (E := E)) := by
          exact (neg_smul ((2 : ℝ)⁻¹) (spectral_epsilon (E := E)))
    _ = -spectral_epsilonHalf (E := E) := by
          simp [spectral_epsilonHalf]

/-- Normalized commutator relation `[I', ε'] = J'`. -/
theorem clmComm_complex_iHalf_spectral_epsilonHalf :
    clmComm (complex_iHalf (E := E)) (spectral_epsilonHalf (E := E))
      = modular_jHalf (E := E) := by
  rw [complex_iHalf, spectral_epsilonHalf, modular_jHalf]
  rw [clmComm_smul (E := E) ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹)
        (complex_i (E := E)) (spectral_epsilon (E := E))]
  rw [clmComm_complex_i_spectral_epsilon (E := E)]
  simp [smul_smul]

end KreinClifford

end InfoGeometry.Krein

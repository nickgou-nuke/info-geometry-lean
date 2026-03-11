import InfoGeometry.Krein.Grading

namespace InfoGeometry.Krein

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def dilationOperator : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • clmComm (modular_j (E := E)) (spectral_epsilon (E := E))

theorem clmComm_modular_j_spectral_epsilon :
    clmComm (modular_j (E := E)) (spectral_epsilon (E := E)) = (2 : ℝ) • complex_i (E := E) := by
  ext v <;> simp [clmComm, complex_i, modular_j, spectral_epsilon, two_smul, sub_eq_add_neg]

@[simp] theorem dilationOperator_eq_complex_i : dilationOperator (E := E) = complex_i (E := E) := by
  rw [dilationOperator, clmComm_modular_j_spectral_epsilon]
  simp [smul_smul]

theorem clmComm_complex_i_modular_j :
    clmComm (complex_i (E := E)) (modular_j (E := E)) = (-2 : ℝ) • spectral_epsilon (E := E) := by
  ext v <;> simp [clmComm, complex_i, modular_j, spectral_epsilon, two_smul, sub_eq_add_neg]

theorem clmComm_complex_i_spectral_epsilon :
    clmComm (complex_i (E := E)) (spectral_epsilon (E := E)) = (2 : ℝ) • modular_j (E := E) := by
  ext v <;> simp [clmComm, complex_i, modular_j, spectral_epsilon, two_smul, sub_eq_add_neg]

noncomputable def modular_jHalf : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • modular_j (E := E)
noncomputable def spectral_epsilonHalf : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • spectral_epsilon (E := E)
noncomputable def complex_iHalf : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • complex_i (E := E)

lemma clmComm_smul (a b : ℝ) (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm (a • A) (b • B) = (a * b) • clmComm A B := by
  ext v <;> simp [clmComm, smul_sub, smul_smul, mul_comm]

theorem clmComm_modular_jHalf_spectral_epsilonHalf :
    clmComm (modular_jHalf (E := E)) (spectral_epsilonHalf (E := E)) = complex_iHalf (E := E) := by
  rw [modular_jHalf, spectral_epsilonHalf, complex_iHalf, clmComm_smul, clmComm_modular_j_spectral_epsilon]
  simp [smul_smul]

end InfoGeometry.Krein

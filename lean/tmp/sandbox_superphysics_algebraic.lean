import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.Grading

namespace InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Prove complex_i is odd algebraically without coordinates. -/
lemma complex_i_isOdd_algebraic : isOdd (E := E) (complex_i (E := E)) := by
  unfold isOdd
  have hleft :
      (modular_j (E := E)).comp (complex_i (E := E))
        = spectral_epsilon (E := E) := by
    unfold complex_i
    rw [← ContinuousLinearMap.comp_assoc, modular_j_involution, ContinuousLinearMap.id_comp]

  have hright :
      (complex_i (E := E)).comp (modular_j (E := E))
        = -(spectral_epsilon (E := E)) := by
    unfold complex_i
    rw [modular_j_spectral_epsilon_anticommute]
    simp [ContinuousLinearMap.comp_assoc, modular_j_involution]

  rw [hleft, hright]
  simp

end InfoGeometry.Krein

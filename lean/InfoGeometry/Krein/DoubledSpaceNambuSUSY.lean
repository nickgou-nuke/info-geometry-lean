import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Krein.DoubledSpaceNambuSUSY

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! The original `Cl(1,1)` involution is recovered from the Hestenes axis
and the spectral involution.  This is the internal Krein symmetry; it is not
the external Nambu grading. -/

theorem modular_j_eq_complex_i_comp_spectral_epsilon :
    modular_j (E := E) =
      (complex_i (E := E)).comp (spectral_epsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [complex_i, modular_j, spectral_epsilon]

theorem complex_i_anticommutes_spectral_epsilon :
    (complex_i (E := E)).comp (spectral_epsilon (E := E)) =
      -(spectral_epsilon (E := E)).comp (complex_i (E := E)) := by
  rw [complex_i_comp_spectral_epsilon, spectral_epsilon_comp_complex_i]
  simp

theorem krein_symmetry_sq :
    (modular_j (E := E)).comp modular_j =
      ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  modular_j_involution (E := E)

end InfoGeometry.Krein.DoubledSpaceNambuSUSY

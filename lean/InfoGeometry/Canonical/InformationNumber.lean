import InfoGeometry.Canonical.Drazin
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dimension.Finite
set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.InformationNumber

open InfoGeometry.Canonical.Drazin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/--
The Information Number Operator N.
Defined as the effective rank (image dimension) of the Drazin spectral projector.
N = dim(Im(a * a^D)).
In a degenerate belief space, this operator counts the number of
 effective (non-singular) parameters.
-/
noncomputable def informationNumber (a a_d : E →L[ℝ] E) (_h : IsDrazinInverse a a_d 1) : ℝ :=
  (Module.finrank ℝ (LinearMap.range (IsDrazinInverse.projection a a_d).toLinearMap) : ℝ)

/-- The information number is always a nonnegative real rank. -/
theorem informationNumber_nonneg
    (a a_d : E →L[ℝ] E) (h : IsDrazinInverse a a_d 1) :
    0 ≤ informationNumber a a_d h := by
  unfold informationNumber
  exact_mod_cast (Nat.zero_le (Module.finrank ℝ
    (LinearMap.range (IsDrazinInverse.projection a a_d).toLinearMap)))

/-- The information number cannot exceed the ambient finite dimension. -/
theorem informationNumber_le_ambientDim
    (a a_d : E →L[ℝ] E) (h : IsDrazinInverse a a_d 1) :
    informationNumber a a_d h ≤ Module.finrank ℝ E := by
  unfold informationNumber
  exact_mod_cast LinearMap.finrank_range_le (IsDrazinInverse.projection a a_d).toLinearMap

/-- The information number is an integer-valued rank bounded by the ambient dimension. -/
theorem exists_natCast_eq_informationNumber
    (a a_d : E →L[ℝ] E) (h : IsDrazinInverse a a_d 1) :
    ∃ n : ℕ, n ≤ Module.finrank ℝ E ∧ informationNumber a a_d h = (n : ℝ) := by
  refine ⟨Module.finrank ℝ (LinearMap.range (IsDrazinInverse.projection a a_d).toLinearMap), ?_, ?_⟩
  · exact LinearMap.finrank_range_le (IsDrazinInverse.projection a a_d).toLinearMap
  · unfold informationNumber
    simp

/-- Surjective Drazin projection saturates the full ambient information number. -/
theorem informationNumber_eq_ambientDim_of_surjectiveProjection
    (a a_d : E →L[ℝ] E) (h : IsDrazinInverse a a_d 1)
    (hsurj : Function.Surjective (IsDrazinInverse.projection a a_d).toLinearMap) :
    informationNumber a a_d h = Module.finrank ℝ E := by
  have hrange :
      LinearMap.range (IsDrazinInverse.projection a a_d).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  unfold informationNumber
  rw [hrange]
  simp

end InfoGeometry.Canonical.InformationNumber

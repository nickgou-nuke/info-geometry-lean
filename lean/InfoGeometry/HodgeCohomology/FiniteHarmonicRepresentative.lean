import InfoGeometry.HodgeCohomology.HodgeDirac
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped InnerProductSpace

namespace InfoGeometry.HodgeCohomology.FiniteHarmonicRepresentative

open HodgeDirac

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [FiniteDimensional ℝ Space]

theorem existsUnique_closed_coclosed_representative
    (differential : Space →ₗ[ℝ] Space) (nilpotent : differential * differential = 0)
    (state : Space) (closed : differential state = 0) :
    ∃! representative : Space,
      differential representative = 0 ∧ differential.adjoint representative = 0 ∧
        ∃ primitive, differential primitive = state - representative := by
  obtain ⟨exactPart, in_range, representative, orthogonal, decomposition⟩ :=
    (LinearMap.range differential).exists_add_mem_mem_orthogonal state
  obtain ⟨primitive, primitive_image⟩ := in_range
  have representative_coclosed : differential.adjoint representative = 0 := by
    apply ext_inner_left ℝ
    intro test
    rw [differential.adjoint_inner_right, inner_zero_right]
    exact ((LinearMap.range differential).mem_orthogonal representative).mp orthogonal
      (differential test) ⟨test, rfl⟩
  have representative_closed : differential representative = 0 := by
    have square_zero : differential (differential primitive) = 0 :=
      LinearMap.congr_fun nilpotent primitive
    have mapped := congrArg differential decomposition
    rw [← primitive_image, map_add, square_zero, zero_add, closed] at mapped
    exact mapped.symm
  have chosen_exact : differential primitive = state - representative := by
    rw [primitive_image, decomposition]
    abel
  refine ⟨representative, ⟨representative_closed, representative_coclosed,
    primitive, chosen_exact⟩, ?_⟩
  rintro alternative ⟨_, alternative_coclosed, alternativePrimitive, alternative_exact⟩
  have exact_difference : differential (primitive - alternativePrimitive) =
      alternative - representative := by
    rw [map_sub, chosen_exact, alternative_exact]
    abel
  have coclosed_difference : differential.adjoint (alternative - representative) = 0 := by
    rw [map_sub, alternative_coclosed, representative_coclosed, sub_self]
  exact sub_eq_zero.mp (coclosed_exact_eq_zero differential differential.adjoint
    (native_adjunction differential) _ _ exact_difference coclosed_difference)

theorem nonzero_harmonic_not_exact (differential : Space →ₗ[ℝ] Space) (state : Space)
    (harmonic : (differential * differential.adjoint + differential.adjoint * differential)
      state = 0) (nonzero : state ≠ 0) :
    state ∉ LinearMap.range differential := by
  rintro ⟨primitive, exact_state⟩
  have coclosed := ((harmonic_iff_closed_and_coclosed differential differential.adjoint
    (native_adjunction differential) state).mp harmonic).2
  exact nonzero (coclosed_exact_eq_zero differential differential.adjoint
    (native_adjunction differential) primitive state exact_state coclosed)

end InfoGeometry.HodgeCohomology.FiniteHarmonicRepresentative

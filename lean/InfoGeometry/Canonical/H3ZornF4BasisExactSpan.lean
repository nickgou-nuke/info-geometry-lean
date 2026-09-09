import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace InfoGeometry.Canonical.H3ZornF4BasisExactSpan

variable {K : Type*} [DivisionRing K]
variable {E F : Type*} [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

theorem range_eq_top_of_section
    (ev : E →ₗ[K] F) (σ : F →ₗ[K] E) (h_sec : ∀ y, ev (σ y) = y) :
    LinearMap.range ev = ⊤ := by
  ext y
  simp only [Submodule.mem_top, iff_true, LinearMap.mem_range]
  exact ⟨σ y, h_sec y⟩

theorem finrank_of_linear_split
    [Module.Finite K E]
    (ev : E →ₗ[K] F) (σ : F →ₗ[K] E) (h_sec : ∀ y, ev (σ y) = y) :
    Module.finrank K E = Module.finrank K (LinearMap.ker ev) + Module.finrank K F := by
  have h_rn := LinearMap.finrank_range_add_finrank_ker ev
  have h_range : LinearMap.range ev = ⊤ := range_eq_top_of_section ev σ h_sec
  rw [h_range, finrank_top] at h_rn
  omega

theorem finrank_off_diagonal_octonions
    (O : Type*) [AddCommGroup O] [Module K O] [Module.Finite K O]
    (hO : Module.finrank K O = 8) :
    Module.finrank K (O × (O × O)) = 24 := by
  simp [Module.finrank_prod, hO]

theorem finrank_ker_of_triality
    {SO8 : Type*} [AddCommGroup SO8] [Module K SO8]
    (ev : E →ₗ[K] F)
    (e_triality : LinearMap.ker ev ≃ₗ[K] SO8)
    (h_so8 : Module.finrank K SO8 = 28) :
    Module.finrank K (LinearMap.ker ev) = 28 := by
  rw [LinearEquiv.finrank_eq e_triality, h_so8]

theorem finrank_f4_exact
    [Module.Finite K E]
    {O : Type*} [AddCommGroup O] [Module K O] [Module.Finite K O] (hO : Module.finrank K O = 8)
    {SO8 : Type*} [AddCommGroup SO8] [Module K SO8] (h_so8 : Module.finrank K SO8 = 28)
    (ev : E →ₗ[K] (O × (O × O)))
    (σ : (O × (O × O)) →ₗ[K] E)
    (h_sec : ∀ y, ev (σ y) = y)
    (e_triality : LinearMap.ker ev ≃ₗ[K] SO8) :
    Module.finrank K E = 52 := by
  have h_split := finrank_of_linear_split ev σ h_sec
  have h_ker := finrank_ker_of_triality ev e_triality h_so8
  have h_off := finrank_off_diagonal_octonions O hO
  rw [h_split, h_ker, h_off]

theorem finrank_f4_real
    {F4 : Type*} [AddCommGroup F4] [Module ℝ F4] [Module.Finite ℝ F4]
    {Oct : Type*} [AddCommGroup Oct] [Module ℝ Oct] [Module.Finite ℝ Oct] (hOct : Module.finrank ℝ Oct = 8)
    {SO8 : Type*} [AddCommGroup SO8] [Module ℝ SO8] (hSO8 : Module.finrank ℝ SO8 = 28)
    (ev : F4 →ₗ[ℝ] (Oct × (Oct × Oct)))
    (σ : (Oct × (Oct × Oct)) →ₗ[ℝ] F4)
    (h_sec : ∀ y, ev (σ y) = y)
    (e_tri : LinearMap.ker ev ≃ₗ[ℝ] SO8) :
    Module.finrank ℝ F4 = 52 :=
  finrank_f4_exact hOct hSO8 ev σ h_sec e_tri

end InfoGeometry.Canonical.H3ZornF4BasisExactSpan

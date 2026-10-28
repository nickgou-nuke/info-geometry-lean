/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.OperatorDirichletLaplacian
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# The positive spectral gap away from the actual Dirichlet kernel

In finite dimension, compactness of the unit sphere constructs a positive
quadratic bound on the orthogonal complement of the kernel. This yields an
exclusion interval in the native spectrum. The kernel is retained, and the
constant belongs to the fixed family of maps, not to an unrestricted family.
-/

noncomputable section

open scoped BigOperators InnerProductSpace
open ContinuousLinearMap

namespace InfoGeometry.Analysis.OperatorDirichletLaplacian

variable {ι E F : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The genuine Hilbert orthogonal complement of the constructed operator's kernel. -/
def kernelOrthogonal (T : ι → E →L[ℂ] F) : Submodule ℂ E :=
  (laplacian T).kerᗮ

theorem energy_pos_of_mem_kernelOrthogonal (T : ι → E →L[ℂ] F)
    {x : E} (hx : x ∈ kernelOrthogonal T) (hx0 : x ≠ 0) :
    0 < energy T x := by
  have hne : energy T x ≠ 0 := by
    intro hzero
    have hker : x ∈ (laplacian T).ker :=
      (laplacian_apply_eq_zero_iff T x).mpr ((energy_eq_zero_iff T x).mp hzero)
    have hinner : inner ℂ x x = 0 :=
      (laplacian T).ker.inner_right_of_mem_orthogonal hker hx
    exact hx0 (inner_self_eq_zero.mp hinner)
  exact lt_of_le_of_ne (energy_nonneg T x) (Ne.symm hne)

/-- Every fixed finite-dimensional family has a positive bound after its full kernel is removed. -/
theorem exists_positive_coercive_bound [FiniteDimensional ℂ E]
    (T : ι → E →L[ℂ] F) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ kernelOrthogonal T,
      c * ‖x‖ ^ 2 ≤ energy T x := by
  let K := kernelOrthogonal T
  let : ProperSpace K := FiniteDimensional.proper ℂ K
  have hcont : Continuous (fun x : K => energy T (x : E)) := by
    unfold energy
    fun_prop
  have hpos : ∀ x ∈ Metric.sphere (0 : K) 1, 0 < energy T (x : E) := by
    intro x hx
    apply energy_pos_of_mem_kernelOrthogonal T x.property
    intro hzero
    have hxzero : x = 0 := Subtype.ext hzero
    simp [hxzero] at hx
  obtain ⟨c, hc, hbound⟩ :=
    (isCompact_sphere (0 : K) 1).exists_forall_le' hcont.continuousOn hpos
  refine ⟨c, hc, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst x
    simp [energy]
  let y : K := ⟨x, hx⟩
  let u : K := ‖y‖⁻¹ • y
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hu : u ∈ Metric.sphere (0 : K) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [u]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
    exact hn
  have he : energy T (u : E) = (‖x‖⁻¹) ^ 2 * energy T x := by
    change energy T (‖x‖⁻¹ • x) = _
    exact energy_smul_real T _ x
  calc
    c * ‖x‖ ^ 2 = ‖x‖ ^ 2 * c := mul_comm _ _
    _ ≤ ‖x‖ ^ 2 * energy T (u : E) :=
      mul_le_mul_of_nonneg_left (hbound u hu) (sq_nonneg _)
    _ = energy T x := by rw [he]; field_simp

/-- Every nonzero eigenvalue has its eigenvectors in the actual kernel complement. -/
theorem eigenvector_mem_kernelOrthogonal (T : ι → E →L[ℂ] F)
    {μ : ℂ} (hμ : μ ≠ 0) {x : E} (hx : laplacian T x = μ • x) :
    x ∈ kernelOrthogonal T := by
  apply ((laplacian T).ker.mem_orthogonal x).mpr
  intro y hy
  have hinner : inner ℂ y (laplacian T x) = 0 := by
    rw [← (isPositive_laplacian T).inner_left_eq_inner_right]
    rw [show laplacian T y = 0 from hy, inner_zero_left]
  rw [hx, inner_smul_right] at hinner
  exact (mul_eq_zero.mp hinner).resolve_left hμ

/-- A proved quadratic bound controls every nonzero eigenvalue of the native operator. -/
theorem re_eigenvalue_ge_of_coercive_bound (T : ι → E →L[ℂ] F)
    {c : ℝ} (hbound : ∀ x ∈ kernelOrthogonal T, c * ‖x‖ ^ 2 ≤ energy T x)
    {μ : ℂ} (hμ : μ ≠ 0) {x : E} (hx0 : x ≠ 0)
    (hx : laplacian T x = μ • x) : c ≤ μ.re := by
  have h := hbound x (eigenvector_mem_kernelOrthogonal T hμ hx)
  have he : energy T x = μ.re * ‖x‖ ^ 2 := by
    rw [← re_inner_laplacian, hx, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  rw [he] at h
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mp h

/-- Compactness constructs a true gap in the native spectrum away from zero. -/
theorem exists_positive_spectral_gap [FiniteDimensional ℂ E]
    (T : ι → E →L[ℂ] F) :
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ spectrum ℂ (laplacian T),
      μ = 0 ∨ c ≤ μ.re := by
  obtain ⟨c, hc, hbound⟩ := exists_positive_coercive_bound T
  refine ⟨c, hc, fun μ hμ => ?_⟩
  by_cases hz : μ = 0
  · exact Or.inl hz
  · right
    rw [ContinuousLinearMap.spectrum_eq] at hμ
    obtain ⟨x, hx⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hμ).exists_hasEigenvector
    exact re_eigenvalue_ge_of_coercive_bound T hbound hz hx.2 hx.apply_eq_smul

/-- The positive real interval below the constructed bound contains no spectral value. -/
theorem exists_positive_spectral_interval [FiniteDimensional ℂ E]
    (T : ι → E →L[ℂ] F) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → r < c →
      (r : ℂ) ∉ spectrum ℂ (laplacian T) := by
  obtain ⟨c, hc, hgap⟩ := exists_positive_spectral_gap T
  refine ⟨c, hc, fun r hr hrc hspec => ?_⟩
  rcases hgap (r : ℂ) hspec with hz | hge
  · exact hr.ne' (Complex.ofReal_eq_zero.mp hz)
  · exact hrc.not_ge (by simpa using hge)

end InfoGeometry.Analysis.OperatorDirichletLaplacian

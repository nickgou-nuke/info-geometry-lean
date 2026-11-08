/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Order.Compact

/-!
# Real positive operators away from their entire kernel

The quadratic form of a native positive real operator vanishes exactly on
its kernel. In finite dimension, compactness of the unit sphere in the
orthogonal complement constructs a positive coercivity bound. The same
bound excludes nonzero real spectral values below it.

The compactness theorem also covers an empty unit sphere. Thus the existence
of the bound does not assert that the kernel complement or the nonzero
spectrum is nonempty.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealPositiveOperatorGap

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic form of a positive real operator detects its full kernel. -/
theorem inner_apply_eq_zero_iff (T : Module.End ℝ E) (hT : T.IsPositive) (x : E) :
    inner ℝ x (T x) = 0 ↔ T x = 0 := by
  let B : LinearMap.BilinForm ℝ E := (innerₗ E).comp T
  have hBn : ∀ y, 0 ≤ B y y := fun y => hT.inner_nonneg_left y
  have hBs : LinearMap.IsSymm B := by
    refine ⟨fun y z => ?_⟩
    change inner ℝ (T y) z = inner ℝ (T z) y
    exact (hT.isSymmetric y z).trans (real_inner_comm (T z) y)
  constructor
  · intro hx
    have hBx : B x x = 0 := by
      change inner ℝ (T x) x = 0
      exact (real_inner_comm x (T x)).trans hx
    have hk : B x = 0 :=
      (B.apply_apply_same_eq_zero_iff hBn hBs).mp hBx
    have hh := congrArg (fun f : E →ₗ[ℝ] ℝ => f (T x)) hk
    change inner ℝ (T x) (T x) = 0 at hh
    exact inner_self_eq_zero.mp hh
  · intro hx
    simp only [hx, inner_zero_right]

/-- Every nonzero vector orthogonal to the kernel has strictly positive energy. -/
theorem inner_pos_of_mem_ker_orthogonal (T : Module.End ℝ E) (hT : T.IsPositive)
    {x : E} (hx : x ∈ T.kerᗮ) (hx0 : x ≠ 0) :
    0 < inner ℝ x (T x) := by
  apply lt_of_le_of_ne (hT.inner_nonneg_right x)
  intro hz
  have hker : x ∈ T.ker := (inner_apply_eq_zero_iff T hT x).mp hz.symm
  exact hx0 (inner_self_eq_zero.mp (T.ker.inner_right_of_mem_orthogonal hker hx))

/-- Compactness constructs a positive bound for each fixed finite-dimensional operator. -/
theorem exists_positive_coercive_bound [FiniteDimensional ℝ E]
    (T : Module.End ℝ E) (hT : T.IsPositive) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ T.kerᗮ,
      δ * ‖x‖ ^ 2 ≤ inner ℝ x (T x) := by
  classical
  let K := T.kerᗮ
  let : ProperSpace K := FiniteDimensional.proper ℝ K
  have hcont : Continuous (fun x : K => inner ℝ (x : E) (T (x : E))) :=
    continuous_subtype_val.inner
      (T.continuous_of_finiteDimensional.comp continuous_subtype_val)
  have hpos : ∀ x ∈ Metric.sphere (0 : K) 1,
      0 < inner ℝ (x : E) (T (x : E)) := by
    intro x hx
    apply inner_pos_of_mem_ker_orthogonal T hT x.property
    intro hzero
    have hxzero : x = 0 := Subtype.ext hzero
    simp [hxzero] at hx
  obtain ⟨δ, hδ, hbound⟩ :=
    (isCompact_sphere (0 : K) 1).exists_forall_le' hcont.continuousOn hpos
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst x
    simp
  let y : K := ⟨x, hx⟩
  let z : K := ‖y‖⁻¹ • y
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hz : z ∈ Metric.sphere (0 : K) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [z]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
    exact hn
  have he : inner ℝ (z : E) (T (z : E)) =
      (‖x‖⁻¹) ^ 2 * inner ℝ x (T x) := by
    change inner ℝ (‖x‖⁻¹ • x) (T (‖x‖⁻¹ • x)) = _
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, pow_two, mul_assoc]
  calc
    δ * ‖x‖ ^ 2 = ‖x‖ ^ 2 * δ := mul_comm _ _
    _ ≤ ‖x‖ ^ 2 * inner ℝ (z : E) (T (z : E)) :=
      mul_le_mul_of_nonneg_left (hbound z hz) (sq_nonneg _)
    _ = inner ℝ x (T x) := by
      rw [he, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_mul]

/-- A nonzero eigenvalue of a symmetric operator has its eigenvectors orthogonal to the kernel. -/
theorem eigenvector_mem_ker_orthogonal (T : Module.End ℝ E) (hT : T.IsSymmetric)
    {μ : ℝ} (hμ : μ ≠ 0) {x : E} (hx : T x = μ • x) :
    x ∈ T.kerᗮ := by
  apply (T.ker.mem_orthogonal x).mpr
  intro y hy
  have hinner : inner ℝ y (T x) = 0 := by
    rw [← hT y x, show T y = 0 from hy, inner_zero_left]
  rw [hx, real_inner_smul_right] at hinner
  exact (mul_eq_zero.mp hinner).resolve_left hμ

/-- A bound on the kernel complement controls every nonzero real eigenvalue. -/
theorem eigenvalue_ge_of_coercive_bound (T : Module.End ℝ E) (hT : T.IsSymmetric)
    {δ : ℝ} (hbound : ∀ x ∈ T.kerᗮ, δ * ‖x‖ ^ 2 ≤ inner ℝ x (T x))
    {μ : ℝ} (hμ : μ ≠ 0) {x : E} (hx0 : x ≠ 0) (hx : T x = μ • x) :
    δ ≤ μ := by
  have h := hbound x (eigenvector_mem_ker_orthogonal T hT hμ hx)
  rw [inner_product_apply_eigenvector hx] at h
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hx0))).mp h

/-- The same quadratic bound excludes every nonzero real spectral value below it. -/
theorem spectrum_gap_of_coercive_bound [FiniteDimensional ℝ E]
    (T : Module.End ℝ E) (hT : T.IsSymmetric)
    {δ : ℝ} (hbound : ∀ x ∈ T.kerᗮ, δ * ‖x‖ ^ 2 ≤ inner ℝ x (T x))
    {μ : ℝ} (hμ : μ ∈ spectrum ℝ T) :
    μ = 0 ∨ δ ≤ μ := by
  by_cases hzero : μ = 0
  · exact Or.inl hzero
  · right
    obtain ⟨x, hx⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hμ).exists_hasEigenvector
    exact eigenvalue_ge_of_coercive_bound T hT hbound hzero hx.2 hx.apply_eq_smul

/-- Every fixed finite-dimensional positive real operator has a spectral gap above its kernel. -/
theorem exists_positive_spectral_gap [FiniteDimensional ℝ E]
    (T : Module.End ℝ E) (hT : T.IsPositive) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ spectrum ℝ T, μ = 0 ∨ δ ≤ μ := by
  obtain ⟨δ, hδ, hbound⟩ := exists_positive_coercive_bound T hT
  exact ⟨δ, hδ, fun _ hμ => spectrum_gap_of_coercive_bound T hT.isSymmetric hbound hμ⟩

/-- A positive real interval above zero contains no spectral value of the fixed operator. -/
theorem exists_positive_spectral_interval [FiniteDimensional ℝ E]
    (T : Module.End ℝ E) (hT : T.IsPositive) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ → μ ∉ spectrum ℝ T := by
  obtain ⟨δ, hδ, hgap⟩ := exists_positive_spectral_gap T hT
  refine ⟨δ, hδ, fun μ hμ hμδ hspectrum => ?_⟩
  rcases hgap μ hspectrum with hzero | hge
  · exact hμ.ne' hzero
  · exact hμδ.not_ge hge

end InfoGeometry.Analysis.RealPositiveOperatorGap

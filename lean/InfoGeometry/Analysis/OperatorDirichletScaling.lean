/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.OperatorDirichletSpectralGap
import Mathlib.Tactic.Linarith

/-!
# Scaling preserves the Dirichlet kernel but prevents a uniform positive bound

The family consists of the actual bounded operators `r • T i`. Every nonzero
real scaling preserves the joint kernel and its orthogonal complement, while
the constructed Laplacian and its energy scale quadratically. Thus a positive
bound for each fixed family does not yield one common positive bound over all
positive scalings. No scalar operator, diagonalization, or commutativity
restriction is introduced.
-/

noncomputable section

namespace InfoGeometry.Analysis.OperatorDirichletLaplacian

variable {ι E F : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A nonzero scaling changes no zero mode of the actual Dirichlet operator. -/
theorem ker_laplacian_smul_real (T : ι → E →L[ℂ] F) {r : ℝ} (hr : r ≠ 0) :
    (laplacian (fun i => r • T i)).ker = (laplacian T).ker := by
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    laplacian_apply_eq_zero_iff, smul_apply]
  simp [hr]

/-- The subspace on which a coercive bound is sought is preserved as well. -/
theorem kernelOrthogonal_smul_real (T : ι → E →L[ℂ] F) {r : ℝ} (hr : r ≠ 0) :
    kernelOrthogonal (fun i => r • T i) = kernelOrthogonal T := by
  unfold kernelOrthogonal
  rw [ker_laplacian_smul_real T hr]

/-- Every output of the constructed self-adjoint operator is orthogonal to its kernel. -/
theorem laplacian_mem_kernelOrthogonal (T : ι → E →L[ℂ] F) (y : E) :
    laplacian T y ∈ kernelOrthogonal T := by
  apply ((laplacian T).ker.mem_orthogonal _).mpr
  intro z hz
  rw [← (isPositive_laplacian T).inner_left_eq_inner_right]
  rw [show laplacian T z = 0 from hz, inner_zero_left]

/-- Positive energy supplies a concrete nonzero vector in the kernel complement:
the image of that vector under the actual Dirichlet operator. -/
theorem exists_nonzero_mem_kernelOrthogonal_of_energy_pos
    (T : ι → E →L[ℂ] F) {y : E} (hy : 0 < energy T y) :
    ∃ x : E, x ∈ kernelOrthogonal T ∧ x ≠ 0 := by
  refine ⟨laplacian T y, laplacian_mem_kernelOrthogonal T y, ?_⟩
  intro hz
  rw [← re_inner_laplacian T y, hz] at hy
  simp at hy

omit [CompleteSpace E] [CompleteSpace F] in
/-- Along every nonzero vector, positive rescaling makes the true Dirichlet
energy smaller than any prescribed positive quadratic bound. -/
theorem exists_positive_scaling_energy_lt (T : ι → E →L[ℂ] F)
    (x : E) (hx : x ≠ 0) (c : ℝ) (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧
      energy (fun i => r • T i) x < c * ‖x‖ ^ 2 := by
  let e := energy T x
  let q := c * ‖x‖ ^ 2
  have he : 0 ≤ e := energy_nonneg T x
  have hq : 0 < q := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hx))
  have hden : 0 < e + 1 := by linarith
  let r := min 1 (q / (e + 1))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hq hden)
  have hrone : r ≤ 1 := min_le_left _ _
  have hrq : r * (e + 1) ≤ q :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hrsq : r ^ 2 ≤ r := by nlinarith
  refine ⟨r, hr, ?_⟩
  rw [energy_family_smul_real]
  exact (mul_le_mul_of_nonneg_right hrsq he).trans_lt (by nlinarith)

/-- No positive coercivity constant works for all positive scalings when
the actual kernel complement contains a nonzero vector. -/
theorem not_exists_uniform_positive_coercive_bound (T : ι → E →L[ℂ] F)
    (hactive : ∃ x : E, x ∈ kernelOrthogonal T ∧ x ≠ 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r →
      ∀ x ∈ kernelOrthogonal (fun i => r • T i),
        c * ‖x‖ ^ 2 ≤ energy (fun i => r • T i) x := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨x, hx, hx0⟩ := hactive
  obtain ⟨r, hr, hsmall⟩ := exists_positive_scaling_energy_lt T x hx0 c hc
  have hxscaled : x ∈ kernelOrthogonal (fun i => r • T i) := by
    rw [kernelOrthogonal_smul_real T hr.ne']
    exact hx
  exact hsmall.not_ge (hbound r hr x hxscaled)

/-- The exact operator-norm scaling of the constructed family. -/
theorem norm_laplacian_smul_real (T : ι → E →L[ℂ] F) (r : ℝ) :
    ‖laplacian (fun i => r • T i)‖ = r ^ 2 * ‖laplacian T‖ := by
  rw [laplacian_smul_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_self_nonneg r), pow_two]

/-- The full operators, rather than only one scalar energy readout, converge to zero. -/
theorem tendsto_laplacian_smul_real_zero (T : ι → E →L[ℂ] F) :
    Filter.Tendsto (fun r : ℝ => laplacian (fun i => r • T i))
      (nhds 0) (nhds 0) := by
  have h : Continuous (fun r : ℝ => (r * r) • laplacian T) := by fun_prop
  simpa only [laplacian_smul_real, zero_mul, zero_smul] using h.tendsto 0

end InfoGeometry.Analysis.OperatorDirichletLaplacian

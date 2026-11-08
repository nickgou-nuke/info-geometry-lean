/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.OperatorDirichletLaplacian
import InfoGeometry.OperatorAlgebra.TracialGNSCommutator
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Dirichlet operators from commutators on the native tracial GNS space

The operator acts on the existing completed `f.GNS`. Its quadratic form is
the sum of squared GNS commutator norms. Faithfulness is required only when
vanishing of a GNS class is converted into an equality in the coefficient
algebra. In the unital setting the identity class is an actual zero mode.
-/

noncomputable section
open scoped ComplexOrder InnerProductSpace
open InfoGeometry.Analysis.OperatorDirichletLaplacian

namespace PositiveLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
variable (htr : ∀ a b : A, f (a * b) = f (b * a))
variable {ι : Type*} [Fintype ι]

@[simp] theorem tracialCommutatorGNS_coe (H : A) (x : f.PreGNS) :
    f.tracialCommutatorGNS htr H (x : f.GNS) =
      (f.toPreGNS (H * f.ofPreGNS x - f.ofPreGNS x * H) : f.GNS) := by
  simpa only [toPreGNS_ofPreGNS] using
    f.tracialCommutatorGNS_toPreGNS htr H (f.ofPreGNS x)

/-- The actual positive sum of squares of the completed commutator operators. -/
def tracialDirichletGNS (H : ι → A) : f.GNS →L[ℂ] f.GNS :=
  laplacian (fun i => f.tracialCommutatorGNS htr (H i))

theorem tracialDirichletGNS_isSelfAdjoint (H : ι → A) :
    IsSelfAdjoint (f.tracialDirichletGNS htr H) :=
  isSelfAdjoint_laplacian _

theorem tracialDirichletGNS_isPositive (H : ι → A) :
    (f.tracialDirichletGNS htr H).IsPositive :=
  isPositive_laplacian _

/-- The scalar quadratic readout is derived from the bounded operator. -/
theorem re_inner_tracialDirichletGNS (H : ι → A) (x : f.GNS) :
    (inner ℂ x (f.tracialDirichletGNS htr H x)).re =
      ∑ i, ‖f.tracialCommutatorGNS htr (H i) x‖ ^ 2 :=
  re_inner_laplacian _ _

/-- Norms of dense representatives retain the original positive functional. -/
theorem gns_norm_sq_toPreGNS (a : A) :
    ‖(f.toPreGNS a : f.GNS)‖ ^ 2 = (f (star a * a)).re := by
  rw [UniformSpace.Completion.norm_coe, preGNS_norm_def]
  exact Real.sq_sqrt (f.map_nonneg (star_mul_self_nonneg a)).1

/-- The exact Dirichlet form on the dense coefficient algebra. -/
theorem re_inner_tracialDirichletGNS_toPreGNS (H : ι → A) (a : A) :
    (inner ℂ (f.toPreGNS a : f.GNS)
      (f.tracialDirichletGNS htr H (f.toPreGNS a))).re =
      ∑ i, (f (star (H i * a - a * H i) * (H i * a - a * H i))).re := by
  rw [f.re_inner_tracialDirichletGNS htr]
  simp only [tracialCommutatorGNS_toPreGNS, gns_norm_sq_toPreGNS]

theorem tracialDirichletGNS_apply_eq_zero_iff (H : ι → A) (x : f.GNS) :
    f.tracialDirichletGNS htr H x = 0 ↔
      ∀ i, f.tracialCommutatorGNS htr (H i) x = 0 :=
  laplacian_apply_eq_zero_iff _ _

/-- No faithfulness is needed for this exact description of the GNS null class. -/
theorem toPreGNS_coe_eq_zero_iff (a : A) :
    (f.toPreGNS a : f.GNS) = 0 ↔ f (star a * a) = 0 := by
  constructor
  · intro ha
    have hn : ‖f.toPreGNS a‖ = 0 := by
      simpa only [UniformSpace.Completion.norm_coe, norm_zero] using congrArg norm ha
    simpa only [hn, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero,
      ofPreGNS_toPreGNS] using (f.preGNS_norm_sq (f.toPreGNS a)).symm
  · intro ha
    apply norm_eq_zero.mp
    rw [UniformSpace.Completion.norm_coe, preGNS_norm_def]
    simp only [ofPreGNS_toPreGNS, ha, Complex.zero_re, Real.sqrt_zero]

/-- Faithfulness is stated on positive squares; it is not assumed as a spectral gap. -/
theorem toPreGNS_coe_eq_zero_iff_of_faithful
    (hfaith : ∀ a : A, f (star a * a) = 0 → a = 0) (a : A) :
    (f.toPreGNS a : f.GNS) = 0 ↔ a = 0 := by
  rw [f.toPreGNS_coe_eq_zero_iff]
  exact ⟨hfaith a, by rintro rfl; simp⟩

/-- The kernel on dense representatives is exactly the joint algebra commutant. -/
theorem tracialDirichletGNS_toPreGNS_eq_zero_iff
    (hfaith : ∀ a : A, f (star a * a) = 0 → a = 0)
    (H : ι → A) (a : A) :
    f.tracialDirichletGNS htr H (f.toPreGNS a) = 0 ↔
      ∀ i, Commute (H i) a := by
  rw [f.tracialDirichletGNS_apply_eq_zero_iff htr]
  simp only [tracialCommutatorGNS_toPreGNS,
    f.toPreGNS_coe_eq_zero_iff_of_faithful hfaith, sub_eq_zero, commute_iff_eq]

/-- Positive commutator energy detects failure to commute with at least one input. -/
theorem re_inner_tracialDirichletGNS_pos_iff
    (hfaith : ∀ a : A, f (star a * a) = 0 → a = 0)
    (H : ι → A) (a : A) :
    0 < (inner ℂ (f.toPreGNS a : f.GNS)
      (f.tracialDirichletGNS htr H (f.toPreGNS a))).re ↔
      ∃ i, ¬ Commute (H i) a := by
  classical
  have hz : (inner ℂ (f.toPreGNS a : f.GNS)
      (f.tracialDirichletGNS htr H (f.toPreGNS a))).re = 0 ↔
      ∀ i, Commute (H i) a := by
    rw [f.re_inner_tracialDirichletGNS htr]
    change energy (fun i => f.tracialCommutatorGNS htr (H i))
      (f.toPreGNS a : f.GNS) = 0 ↔ _
    rw [energy_eq_zero_iff]
    simp only [tracialCommutatorGNS_toPreGNS,
      f.toPreGNS_coe_eq_zero_iff_of_faithful hfaith, sub_eq_zero, commute_iff_eq]
  constructor
  · intro hp
    exact not_forall.mp (fun hc => (ne_of_gt hp) (hz.mpr hc))
  · rintro ⟨i, hi⟩
    have hn : 0 ≤ (inner ℂ (f.toPreGNS a : f.GNS)
        (f.tracialDirichletGNS htr H (f.toPreGNS a))).re := by
      rw [f.re_inner_tracialDirichletGNS htr]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact (lt_iff_le_and_ne).mpr ⟨hn, fun h => hi (hz.mp h.symm i)⟩

/-- Scaling is an equality of completed commutator operators. -/
theorem tracialCommutatorGNS_smul (c : ℂ) (H : A) :
    f.tracialCommutatorGNS htr (c • H) = c • f.tracialCommutatorGNS htr H := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (f.tracialCommutatorGNS htr (c • H)).continuous
      (c • f.tracialCommutatorGNS htr H).continuous
  | ih x =>
    simp [tracialCommutatorGNS_coe, smul_mul_assoc, mul_smul_comm,
      ← smul_sub, UniformSpace.Completion.coe_smul]

theorem tracialCommutatorGNS_smul_real (r : ℝ) (H : A) :
    f.tracialCommutatorGNS htr (r • H) = r • f.tracialCommutatorGNS htr H := by
  convert! f.tracialCommutatorGNS_smul htr (r : ℂ) H using 1

/-- A common real scaling changes the actual Dirichlet operator quadratically. -/
theorem tracialDirichletGNS_smul_real (H : ι → A) (r : ℝ) :
    f.tracialDirichletGNS htr (fun i => r • H i) =
      (r * r) • f.tracialDirichletGNS htr H := by
  simp only [tracialDirichletGNS, tracialCommutatorGNS_smul_real,
    laplacian_smul_real]

/-- Nonzero scaling preserves the whole kernel, even though energies scale quadratically. -/
theorem tracialDirichletGNS_smul_real_apply_eq_zero_iff
    (H : ι → A) (r : ℝ) (hr : r ≠ 0) (x : f.GNS) :
    f.tracialDirichletGNS htr (fun i => r • H i) x = 0 ↔
      f.tracialDirichletGNS htr H x = 0 := by
  rw [f.tracialDirichletGNS_smul_real htr]
  simp only [smul_apply, smul_eq_zero,
    mul_ne_zero hr hr, false_or]

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
variable (htr : ∀ a b : A, f (a * b) = f (b * a))
variable {ι : Type*} [Fintype ι]

/-- The identity class is an actual zero mode of every commutator Dirichlet operator. -/
theorem tracialDirichletGNS_vacuum (H : ι → A) :
    f.tracialDirichletGNS htr H (f.toPreGNS 1) = 0 := by
  rw [f.tracialDirichletGNS_apply_eq_zero_iff htr]
  intro i
  simp only [tracialCommutatorGNS_toPreGNS, mul_one, one_mul, sub_self, map_zero]
  exact UniformSpace.Completion.coe_zero

theorem gns_vacuum_ne_zero (hf : f 1 ≠ 0) : (f.toPreGNS 1 : f.GNS) ≠ 0 := by
  intro h
  apply hf
  simpa using (f.toPreGNS_coe_eq_zero_iff (1 : A)).mp h

/-- The vacuum obstruction appears in the native bounded-operator spectrum. -/
theorem zero_mem_spectrum_tracialDirichletGNS (hf : f 1 ≠ 0) (H : ι → A) :
    (0 : ℂ) ∈ spectrum ℂ (f.tracialDirichletGNS htr H) := by
  apply (spectrum.zero_mem_iff ℂ).mpr
  intro hunit
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  apply f.gns_vacuum_ne_zero hf
  apply hinj
  simpa using f.tracialDirichletGNS_vacuum htr H

end Unital

end PositiveLinearMap

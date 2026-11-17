/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KuboMoriBogoliubovMetric
import InfoGeometry.Algebra.MatrixNoncommutativity
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strictly positive real Kubo--Mori form on full matrix observables

The existing density owner records positive normalized eigenvalues. This file
discharges its formerly supplied positivity condition for every logarithmic-mean
weight, constructs a native real bilinear form, and proves positive definiteness
on all real matrices. Neither observable is required to commute with the density
or with the other observable. Orthogonal conjugation transports the entire
matrix algebra to another real frame.

The weights are also identified with their real interpolation integrals. This is
the Kubo--Mori response on observables; the inverse response is the corresponding
density-tangent metric. No entropy trajectory or convergence theorem is asserted.
-/

noncomputable section

namespace KuboMoriBogoliubov.FaithfulDensityState

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (rho : FaithfulDensityState n)

/-- Every logarithmic-mean weight is strictly positive, including off-diagonal
entries with unequal eigenvalues. -/
theorem bkm_weight_pos (i j : n) : 0 < rho.bkmWeight i j := by
  unfold bkmWeight
  split_ifs with h
  · exact rho.p_pos i
  · rcases lt_or_gt_of_ne h with hij | hji
    · exact div_pos_of_neg_of_neg (sub_neg.mpr hij)
        (sub_neg.mpr (Real.log_lt_log (rho.p_pos i) hij))
    · exact div_pos (sub_pos.mpr hji)
        (sub_pos.mpr (Real.log_lt_log (rho.p_pos j) hji))

/-- The unconditional nonnegativity theorem on the full matrix carrier. -/
theorem bkmInnerProduct_nonneg (A : Matrix n n ℝ) :
    0 ≤ rho.bkmInnerProduct A A :=
  rho.bkm_metric_pos_semidef_diag A (fun i j => (rho.bkm_weight_pos i j).le)

/-- A nonzero entry contributes a strictly positive summand. -/
theorem bkmInnerProduct_pos (A : Matrix n n ℝ) (hA : A ≠ 0) :
    0 < rho.bkmInnerProduct A A := by
  have hentry : ∃ i j, A j i ≠ 0 := by
    by_contra! h
    apply hA
    ext i j
    exact h j i
  obtain ⟨i, j, hij⟩ := hentry
  unfold bkmInnerProduct
  apply Finset.sum_pos'
  · intro k _
    exact Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_self_nonneg (A l k)) (rho.bkm_weight_pos k l).le
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.sum_pos'
    · intro l _
      exact mul_nonneg (mul_self_nonneg (A l i)) (rho.bkm_weight_pos i l).le
    · exact ⟨j, Finset.mem_univ j,
        mul_pos (mul_self_pos.mpr hij) (rho.bkm_weight_pos i j)⟩

theorem bkmInnerProduct_add_left (A B C : Matrix n n ℝ) :
    rho.bkmInnerProduct (A + B) C =
      rho.bkmInnerProduct A C + rho.bkmInnerProduct B C := by
  simp only [bkmInnerProduct, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem bkmInnerProduct_smul_left (c : ℝ) (A B : Matrix n n ℝ) :
    rho.bkmInnerProduct (c • A) B = c • rho.bkmInnerProduct A B := by
  simp only [bkmInnerProduct, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem bkmInnerProduct_add_right (A B C : Matrix n n ℝ) :
    rho.bkmInnerProduct A (B + C) =
      rho.bkmInnerProduct A B + rho.bkmInnerProduct A C := by
  simp only [bkmInnerProduct, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem bkmInnerProduct_smul_right (c : ℝ) (A B : Matrix n n ℝ) :
    rho.bkmInnerProduct A (c • B) = c • rho.bkmInnerProduct A B := by
  rw [rho.bkm_metric_symmetry A (c • B), rho.bkmInnerProduct_smul_left,
    rho.bkm_metric_symmetry B A]

/-- Native bilinear packaging of the existing real spectral response. -/
def bkmBilinForm : LinearMap.BilinForm ℝ (Matrix n n ℝ) :=
  LinearMap.mk₂ ℝ rho.bkmInnerProduct
    rho.bkmInnerProduct_add_left rho.bkmInnerProduct_smul_left
    rho.bkmInnerProduct_add_right rho.bkmInnerProduct_smul_right

@[simp] theorem bkmBilinForm_apply (A B : Matrix n n ℝ) :
    rho.bkmBilinForm A B = rho.bkmInnerProduct A B := rfl

theorem bkmBilinForm_isSymm : rho.bkmBilinForm.IsSymm :=
  ⟨rho.bkm_metric_symmetry⟩

theorem bkmBilinForm_pos (A : Matrix n n ℝ) (hA : A ≠ 0) :
    0 < rho.bkmBilinForm A A := rho.bkmInnerProduct_pos A hA

/-- Identity insertion is the normalized state expectation. -/
theorem bkmBilinForm_one_left (A : Matrix n n ℝ) :
    rho.bkmBilinForm 1 A = ∑ i, rho.eigenvalues i * A i i := by
  rw [bkmBilinForm_apply]
  unfold bkmInnerProduct
  apply Finset.sum_congr rfl
  intro i _
  have hdiag : rho.bkmWeight i i = rho.eigenvalues i := by
    simp [bkmWeight]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_mul, hdiag]
    exact mul_comm _ _
  · intro j _ hji
    simp only [Matrix.one_apply_ne hji, zero_mul]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem bkmBilinForm_one_one : rho.bkmBilinForm 1 1 = 1 := by
  rw [bkmBilinForm_one_left]
  simpa using rho.p_sum

/-- The weight equals the actual scalar interpolation integral. -/
theorem bkmWeight_eq_integral (i j : n) :
    rho.bkmWeight i j =
      ∫ t : ℝ in (0 : ℝ)..1, rho.eigenvalues i ^ (1 - t) * rho.eigenvalues j ^ t := by
  let p := rho.eigenvalues i
  let q := rho.eigenvalues j
  have hp : 0 < p := rho.p_pos i
  have hq : 0 < q := rho.p_pos j
  change (if p = q then p else (p - q) / (Real.log p - Real.log q)) = _
  by_cases hpq : p = q
  · rw [ite_eq_left hpq]
    have hconst : (fun t : ℝ => p ^ (1 - t) * q ^ t) = fun _ => p := by
      funext t
      rw [← hpq, ← Real.rpow_add hp]
      have hexponent : (1 - t) + t = 1 := by ring
      rw [hexponent, Real.rpow_one]
    change p = ∫ t : ℝ in (0 : ℝ)..1, p ^ (1 - t) * q ^ t
    rw [hconst]
    simp
  · rw [ite_eq_right hpq]
    have hlog : Real.log q - Real.log p ≠ 0 := by
      intro h
      have heq := congrArg Real.exp (sub_eq_zero.mp h)
      rw [Real.exp_log hq, Real.exp_log hp] at heq
      exact hpq heq.symm
    have hintegrand :
        (fun t : ℝ => p ^ (1 - t) * q ^ t) =
          fun t => Real.exp ((Real.log q - Real.log p) * t + Real.log p) := by
      funext t
      rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hq, ← Real.exp_add]
      congr 1
      ring
    change (p - q) / (Real.log p - Real.log q) =
      ∫ t : ℝ in (0 : ℝ)..1, p ^ (1 - t) * q ^ t
    rw [hintegrand, intervalIntegral.integral_comp_mul_add _ hlog,
      _root_.integral_exp]
    simp only [mul_one, sub_add_cancel, mul_zero, zero_add,
      Real.exp_log hp, Real.exp_log hq, smul_eq_mul]
    rw [← div_eq_inv_mul]
    simpa only [neg_sub] using
      (neg_div_neg_eq (p - q) (Real.log p - Real.log q)).symm

/-- The full matrix response is the trace interpolation integral, including
every off-diagonal entry of both observables. -/
theorem bkmInnerProduct_eq_trace_integral (A B : Matrix n n ℝ) :
    rho.bkmInnerProduct A B =
      ∫ t : ℝ in (0 : ℝ)..1,
        Matrix.trace
          (Matrix.diagonal (fun i => rho.eigenvalues i ^ (1 - t)) * A.transpose *
            Matrix.diagonal (fun i => rho.eigenvalues i ^ t) * B) := by
  have hcontinuous (i j : n) : Continuous
      (fun t : ℝ => rho.eigenvalues i ^ (1 - t) * rho.eigenvalues j ^ t) := by
    simp_rw [Real.rpow_def_of_pos (rho.p_pos i),
      Real.rpow_def_of_pos (rho.p_pos j)]
    fun_prop
  have hint (i j : n) : IntervalIntegrable
      (fun t : ℝ => (A j i * B j i) *
        (rho.eigenvalues i ^ (1 - t) * rho.eigenvalues j ^ t))
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hcontinuous i j)).intervalIntegrable _ _
  have hrow (i : n) : IntervalIntegrable
      (fun t : ℝ => ∑ j, (A j i * B j i) *
        (rho.eigenvalues i ^ (1 - t) * rho.eigenvalues j ^ t))
      MeasureTheory.volume 0 1 := by
    simpa only [Finset.sum_fn] using
      (IntervalIntegrable.sum Finset.univ (fun j _ => hint i j))
  have htrace (t : ℝ) :
      Matrix.trace
        (Matrix.diagonal (fun i => rho.eigenvalues i ^ (1 - t)) * A.transpose *
          Matrix.diagonal (fun i => rho.eigenvalues i ^ t) * B) =
        ∑ i, ∑ j, (A j i * B j i) *
          (rho.eigenvalues i ^ (1 - t) * rho.eigenvalues j ^ t) := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
    ring
  simp_rw [htrace]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hrow i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => hint _ j),
    intervalIntegral.integral_const_mul, ← rho.bkmWeight_eq_integral]
  rfl

/-- Real orthogonal change of frame, implemented by the native algebra
automorphism rather than a diagonal restriction of observables. -/
def orthogonalConjugation (U : unitary (Matrix n n ℝ)) :
    Matrix n n ℝ ≃ₗ[ℝ] Matrix n n ℝ :=
  (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U).toAlgEquiv.toLinearEquiv

/-- Pull the full response back from an eigenframe. -/
def bkmBilinFormInFrame (U : unitary (Matrix n n ℝ)) :
    LinearMap.BilinForm ℝ (Matrix n n ℝ) :=
  rho.bkmBilinForm.compl₁₂ (orthogonalConjugation U).symm.toLinearMap
    (orthogonalConjugation U).symm.toLinearMap

theorem bkmBilinFormInFrame_pos (U : unitary (Matrix n n ℝ))
    (A : Matrix n n ℝ) (hA : A ≠ 0) :
    0 < rho.bkmBilinFormInFrame U A A := by
  apply rho.bkmBilinForm_pos
  intro h
  apply hA
  exact (orthogonalConjugation U).symm.injective (h.trans (map_zero _).symm)

theorem bkmBilinFormInFrame_isSymm (U : unitary (Matrix n n ℝ)) :
    (rho.bkmBilinFormInFrame U).IsSymm := by
  constructor
  intro A B
  exact rho.bkmBilinForm_isSymm.eq _ _

theorem bkmBilinFormInFrame_one_one (U : unitary (Matrix n n ℝ)) :
    rho.bkmBilinFormInFrame U 1 1 = 1 := by
  change rho.bkmBilinForm
    ((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U).symm 1)
    ((Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U).symm 1) = 1
  rw [map_one, rho.bkmBilinForm_one_one]

/-- Both observables in the shared closed witness are real symmetric, full
matrices. Their nonzero commutator has strictly positive Kubo--Mori response. -/
theorem noncommuting_pair_has_positive_response
    (density : FaithfulDensityState (Fin 2)) :
    0 < density.bkmBilinForm
      (InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix *
          InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix -
        InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix *
          InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix)
      (InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix *
          InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix -
        InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix *
          InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix) := by
  apply density.bkmBilinForm_pos
  exact sub_ne_zero.mpr
    InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix_mul_tiltedMatrix_ne

end KuboMoriBogoliubov.FaithfulDensityState

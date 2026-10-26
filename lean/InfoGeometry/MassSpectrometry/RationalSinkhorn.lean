/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.SinkhornAssignment
import InfoGeometry.MassSpectrometry.NumericalValidation

/-!
# Executable rational Sinkhorn steps

Finite exact-rational normalization refines the existing real normalization
owner. Iteration is bounded by a caller-supplied count; acceptance is checked
separately. No convergence or floating-point implementation theorem is assumed.
-/

namespace InfoGeometry.MassSpectrometry.RationalSinkhorn

variable {n : ℕ}

def rowNormalize (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => A i j / ∑ l, A i l

def colNormalize (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => A i j / ∑ l, A l j

/-- Total bounded iteration. Zero-sum rows/columns stay zero and cannot pass
an exact unit-sum acceptance check on a nonempty carrier. -/
def iterate : ℕ → Matrix (Fin n) (Fin n) ℚ → Matrix (Fin n) (Fin n) ℚ
  | 0, A => A
  | t + 1, A => colNormalize (rowNormalize (iterate t A))

theorem rowNormalize_sum (A : Matrix (Fin n) (Fin n) ℚ) (i : Fin n)
    (h : ∑ j, A i j ≠ 0) : ∑ j, rowNormalize A i j = 1 := by
  simp only [rowNormalize, ← Finset.sum_div, div_self h]

theorem colNormalize_sum (A : Matrix (Fin n) (Fin n) ℚ) (j : Fin n)
    (h : ∑ i, A i j ≠ 0) : ∑ i, colNormalize A i j = 1 := by
  simp only [colNormalize, ← Finset.sum_div, div_self h]

theorem rowNormalize_nonneg (A : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ i j, 0 ≤ A i j) : ∀ i j, 0 ≤ rowNormalize A i j := by
  intro i j
  exact div_nonneg (h i j) (Finset.sum_nonneg fun l _ => h i l)

theorem colNormalize_nonneg (A : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ i j, 0 ≤ A i j) : ∀ i j, 0 ≤ colNormalize A i j := by
  intro i j
  exact div_nonneg (h i j) (Finset.sum_nonneg fun l _ => h l j)

theorem iterate_nonneg (t : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ i j, 0 ≤ A i j) : ∀ i j, 0 ≤ iterate t A i j := by
  induction t with
  | zero => exact h
  | succ t ih => exact colNormalize_nonneg _ (rowNormalize_nonneg _ ih)

/-- Cast commutes with the existing real row-normalization specification. -/
theorem cast_rowNormalize (A : Matrix (Fin n) (Fin n) ℚ)
    (h : InfoGeometry.Canonical.MoE.HasPositiveRowSums n (fun i j => (A i j : ℝ))) :
    (fun i j => (rowNormalize A i j : ℝ)) =
      InfoGeometry.Canonical.MoE.rowNormalize n (fun i j => (A i j : ℝ)) h := by
  ext i j
  simp [rowNormalize, InfoGeometry.Canonical.MoE.rowNormalize,
    InfoGeometry.Canonical.MoE.rowSum]

/-- Cast commutes with the existing real column-normalization specification. -/
theorem cast_colNormalize (A : Matrix (Fin n) (Fin n) ℚ)
    (h : InfoGeometry.Canonical.MoE.HasPositiveColSums n (fun i j => (A i j : ℝ))) :
    (fun i j => (colNormalize A i j : ℝ)) =
      InfoGeometry.Canonical.MoE.colNormalize n (fun i j => (A i j : ℝ)) h := by
  ext i j
  simp [colNormalize, InfoGeometry.Canonical.MoE.colNormalize,
    InfoGeometry.Canonical.MoE.colSum]

/-- An actually computed iterate accepted at zero tolerance is an exact soft
assignment, regardless of how many iterations were requested. -/
theorem accepted_iterate_soft (t : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (h : NumericalValidation.checkAssignment (iterate t A) 0 = true) :
    IsSoftAssignment (fun i j => (iterate t A i j : ℝ)) :=
  NumericalValidation.checkAssignment_zero_sound _ h

end InfoGeometry.MassSpectrometry.RationalSinkhorn

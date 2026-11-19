/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.TableBalancing
import InfoGeometry.Spectrometry.InteriorLogSlope
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Selecting cartridges before or after normalization

Restricting the rows of a log table changes its geometric sample effects only
by one common additive constant. All contrasts, and regression slopes with
an intercept, are therefore unchanged. The interaction must be recentered
over the retained samples.

Uniform arithmetic balancing is different: an explicit strictly positive
3-by-2 table and its first two rows have different balanced inverse-row-factor
ratios. The example verifies the actual positive factors and target margins.
It makes no inference about measured uncertainties or physical causes.
-/

namespace InfoGeometry.Spectrometry.SpectralRestriction

open scoped BigOperators
open InfoGeometry.Spectrometry.TableBalancing

noncomputable section

def restrictRows {I J S : Type*} (select : S → I) (L : I → J → ℝ) : S → J → ℝ :=
  fun s j => L (select s) j

variable {I J S : Type*} [Fintype I] [Fintype J] [Fintype S]

omit [Fintype I] [Fintype S] in
theorem rowMean_restrictRows (select : S → I) (L : I → J → ℝ) (s : S) :
    rowMean (restrictRows select L) s = rowMean L (select s) := rfl

theorem rowEffect_restrictRows (select : S → I) (L : I → J → ℝ) (s : S) :
    rowEffect (restrictRows select L) s =
      rowEffect L (select s) + (grandMean L - grandMean (restrictRows select L)) := by
  unfold rowEffect
  rw [rowMean_restrictRows]
  ring

theorem rowEffect_contrast_restrictRows (select : S → I) (L : I → J → ℝ)
    (s t : S) :
    rowEffect (restrictRows select L) s - rowEffect (restrictRows select L) t =
      rowEffect L (select s) - rowEffect L (select t) := by
  rw [rowEffect_restrictRows, rowEffect_restrictRows]
  ring

theorem geometricFactor_restrictRows (select : S → I) (L : I → J → ℝ) (s : S) :
    Real.exp (rowEffect (restrictRows select L) s) =
      Real.exp (grandMean L - grandMean (restrictRows select L)) *
        Real.exp (rowEffect L (select s)) := by
  rw [rowEffect_restrictRows, Real.exp_add]
  ring

/-- The spatial predictor, weights, and fit sample set are the same on both
sides. Only the domain used to compute the grand log mean differs. -/
theorem weightedSlope_restrictRows (select : S → I) (L : I → J → ℝ)
    (w x : S → ℝ) (hw : (∑ s, w s) ≠ 0) :
    InteriorLogSlope.weightedSlope w x (rowEffect (restrictRows select L)) =
      InteriorLogSlope.weightedSlope w x (fun s => rowEffect L (select s)) := by
  have hfun : rowEffect (restrictRows select L) =
      fun s => rowEffect L (select s) +
        (grandMean L - grandMean (restrictRows select L)) := by
    funext s
    exact rowEffect_restrictRows select L s
  rw [hfun]
  simpa only [add_comm] using
    InteriorLogSlope.weightedSlope_add_constant w x
      (fun s => rowEffect L (select s)) hw
      (grandMean L - grandMean (restrictRows select L))

variable [Nonempty J] [Nonempty S]

theorem doubleCenter_restrictRows_eq_recenter (select : S → I) (L : I → J → ℝ) :
    doubleCenter (restrictRows select L) =
      doubleCenter (restrictRows select (doubleCenter L)) := by
  have hfun : restrictRows select L =
      addGauge (restrictRows select (doubleCenter L))
        (fun s => rowMean L (select s)) (fun j => colMean L j - grandMean L) := by
    funext s j
    unfold restrictRows addGauge doubleCenter
    ring
  rw [hfun, doubleCenter_addGauge]

/-- A restricted interaction is not generally already centered over its
remaining sample rows. The exact correction is its retained column mean. -/
theorem doubleCenter_restrictRows (select : S → I) (L : I → J → ℝ)
    (s : S) (j : J) :
    doubleCenter (restrictRows select L) s j =
      doubleCenter L (select s) j -
        colMean (restrictRows select (doubleCenter L)) j := by
  have hrow (t : S) : rowMean (restrictRows select (doubleCenter L)) t = 0 :=
    rowMean_doubleCenter L (select t)
  have hgrand : grandMean (restrictRows select (doubleCenter L)) = 0 := by
    change mean (fun t => rowMean (restrictRows select (doubleCenter L)) t) = 0
    simp only [hrow, mean_const]
  rw [doubleCenter_restrictRows_eq_recenter]
  rw [doubleCenter, hrow, hgrand]
  simp only [restrictRows, sub_zero, add_zero]

section ExplicitBalancedCounterexample

def exampleTable : Fin 3 → Fin 2 → ℝ :=
  ![![1, 1], ![1, 4], ![4, 1]]

def exampleFullRows : Fin 3 → ℝ := ![1 / 6, 1 / 15, 1 / 15]
def exampleFullColumns : Fin 2 → ℝ := ![1, 1]

def firstTwo : Fin 2 → Fin 3 :=
  fun i => ⟨i.val, by omega⟩

def exampleRestrictedRows : Fin 2 → ℝ := ![1 / 6, 1 / 12]
def exampleRestrictedColumns : Fin 2 → ℝ := ![2, 1]

theorem exampleTable_pos (i : Fin 3) (j : Fin 2) : 0 < exampleTable i j := by
  fin_cases i <;> fin_cases j <;> norm_num [exampleTable]

theorem exampleFullRows_pos (i : Fin 3) : 0 < exampleFullRows i := by
  fin_cases i <;> norm_num [exampleFullRows]

theorem exampleFullColumns_pos (j : Fin 2) : 0 < exampleFullColumns j := by
  fin_cases j <;> norm_num [exampleFullColumns]

theorem exampleRestrictedRows_pos (i : Fin 2) : 0 < exampleRestrictedRows i := by
  fin_cases i <;> norm_num [exampleRestrictedRows]

theorem exampleRestrictedColumns_pos (j : Fin 2) :
    0 < exampleRestrictedColumns j := by
  fin_cases j <;> norm_num [exampleRestrictedColumns]

theorem example_full_row_margins (i : Fin 3) :
    rowSum (diagonalScale exampleFullRows exampleFullColumns exampleTable) i =
      (1 / 3 : ℝ) := by
  fin_cases i <;>
    norm_num [rowSum, diagonalScale, exampleTable, exampleFullRows,
      exampleFullColumns, Fin.sum_univ_succ]

theorem example_full_column_margins (j : Fin 2) :
    colSum (diagonalScale exampleFullRows exampleFullColumns exampleTable) j =
      (1 / 2 : ℝ) := by
  fin_cases j <;>
    norm_num [colSum, diagonalScale, exampleTable, exampleFullRows,
      exampleFullColumns, Fin.sum_univ_succ]

theorem example_restricted_row_margins (i : Fin 2) :
    rowSum (diagonalScale exampleRestrictedRows exampleRestrictedColumns
      (restrictRows firstTwo exampleTable)) i = (1 / 2 : ℝ) := by
  fin_cases i <;>
    norm_num [rowSum, diagonalScale, restrictRows, firstTwo, exampleTable,
      exampleRestrictedRows, exampleRestrictedColumns, Fin.sum_univ_succ]

theorem example_restricted_column_margins (j : Fin 2) :
    colSum (diagonalScale exampleRestrictedRows exampleRestrictedColumns
      (restrictRows firstTwo exampleTable)) j = (1 / 2 : ℝ) := by
  fin_cases j <;>
    norm_num [colSum, diagonalScale, restrictRows, firstTwo, exampleTable,
      exampleRestrictedRows, exampleRestrictedColumns, Fin.sum_univ_succ]

theorem example_full_inverse_row_ratio :
    (1 / exampleFullRows 0) / (1 / exampleFullRows 1) = (2 / 5 : ℝ) := by
  norm_num [exampleFullRows]

theorem example_restricted_inverse_row_ratio :
    (1 / exampleRestrictedRows 0) / (1 / exampleRestrictedRows 1) = (1 / 2 : ℝ) := by
  norm_num [exampleRestrictedRows]

theorem example_inverse_row_ratio_changes :
    (1 / exampleFullRows 0) / (1 / exampleFullRows 1) ≠
      (1 / exampleRestrictedRows 0) / (1 / exampleRestrictedRows 1) := by
  rw [example_full_inverse_row_ratio, example_restricted_inverse_row_ratio]
  norm_num

end ExplicitBalancedCounterexample
end
end InfoGeometry.Spectrometry.SpectralRestriction

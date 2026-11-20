/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.TableBalancing
import InfoGeometry.Spectrometry.LogInteractionAndGauge
import InfoGeometry.Spectrometry.ColumnFirstSinkhornCovariance

/-!
# Transposing the two spectrometry conventions

The recovered five-channel table has samples as rows and spectral lines as
columns. The earlier two-line development uses the transpose convention.
This module connects the actual centering operators and defines row-first
iterations by transposing the verified column-first iteration.

A sample correction is a row multiplier in the first convention. Identical
initial column potentials therefore give finite row-first covariance. There
is no additional potential gauge recentering or convergence assertion.
-/

namespace InfoGeometry.Spectrometry.SpectralOrientation

open scoped BigOperators
open InfoGeometry.Spectrometry.TableBalancing

noncomputable section

def transpose {I J : Type*} (L : I → J → ℝ) : J → I → ℝ :=
  fun j i => L i j

@[simp] theorem transpose_transpose {I J : Type*} (L : I → J → ℝ) :
    transpose (transpose L) = L := rfl

variable {I J : Type*} [Fintype I] [Fintype J]

/-- These are the same finite operator, despite their independently chosen names. -/
theorem doubleCenter_eq_interaction (L : I → J → ℝ) :
    doubleCenter L = LogInteractionAndGauge.interaction L := rfl

theorem logSumExp_eq_columnFirst (z : J → ℝ) :
    logSumExp z = ColumnFirstSinkhornCovariance.logSumExp z := rfl

omit [Fintype J] in
@[simp] theorem rowMean_transpose (L : I → J → ℝ) (j : J) :
    rowMean (transpose L) j = colMean L j := rfl

omit [Fintype I] in
@[simp] theorem colMean_transpose (L : I → J → ℝ) (i : I) :
    colMean (transpose L) i = rowMean L i := rfl

@[simp] theorem grandMean_transpose (L : I → J → ℝ) :
    grandMean (transpose L) = grandMean L := by
  change mean (colMean L) = grandMean L
  exact mean_colMean L

theorem rowEffect_transpose (L : I → J → ℝ) (j : J) :
    rowEffect (transpose L) j = colEffect L j := by
  simp only [rowEffect, colEffect, rowMean_transpose, grandMean_transpose]

theorem colEffect_transpose (L : I → J → ℝ) (i : I) :
    colEffect (transpose L) i = rowEffect L i := by
  simp only [rowEffect, colEffect, colMean_transpose, grandMean_transpose]

theorem doubleCenter_transpose (L : I → J → ℝ) :
    doubleCenter (transpose L) = transpose (doubleCenter L) := by
  funext j i
  simp only [doubleCenter, rowMean_transpose, colMean_transpose,
    grandMean_transpose, transpose]
  ring

/-- The two-line operator on the transposed table is exactly the transposed
five-channel operator, with no approximation or numerical comparison. -/
theorem interaction_transpose_bridge (L : I → J → ℝ) :
    LogInteractionAndGauge.interaction (transpose L) =
      transpose (doubleCenter L) := by
  rw [← doubleCenter_eq_interaction, doubleCenter_transpose]

/-- With exactly two channels, row centering forces opposite interaction columns. -/
theorem twoChannel_interaction_opposite (L : I → Fin 2 → ℝ) (i : I) :
    doubleCenter L i 1 = -doubleCenter L i 0 := by
  have h := rowMean_doubleCenter L i
  norm_num [rowMean, mean, Fin.sum_univ_succ] at h
  linarith

/-- The two-channel interaction has vanishing minors for every log table.
This fact alone therefore cannot identify a loading mechanism. -/
theorem twoChannel_interaction_minor (L : I → Fin 2 → ℝ)
    (i k : I) (j l : Fin 2) :
    doubleCenter L i j * doubleCenter L k l -
      doubleCenter L i l * doubleCenter L k j = 0 := by
  fin_cases j <;> fin_cases l
  · ring
  · change doubleCenter L i 0 * doubleCenter L k 1 -
      doubleCenter L i 1 * doubleCenter L k 0 = 0
    rw [twoChannel_interaction_opposite, twoChannel_interaction_opposite]
    ring
  · change doubleCenter L i 1 * doubleCenter L k 0 -
      doubleCenter L i 0 * doubleCenter L k 1 = 0
    rw [twoChannel_interaction_opposite, twoChannel_interaction_opposite]
    ring
  · ring

def rowShift (L : I → J → ℝ) (d : I → ℝ) : I → J → ℝ :=
  fun i j => L i j + d i

omit [Fintype I] [Fintype J] in
theorem transpose_rowShift (L : I → J → ℝ) (d : I → ℝ) :
    transpose (rowShift L d) =
      ColumnFirstSinkhornCovariance.columnShift (transpose L) d := rfl

/-- Column potential before the next row update; k=0 is the supplied initial value. -/
def columnPotential (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) : J → ℝ :=
  ColumnFirstSinkhornCovariance.rowPotential
    (transpose L) logColumns logRows initialColumn k

/-- Row potential after the next row update; k=0 already includes one row update. -/
def rowPotential (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) : I → ℝ :=
  ColumnFirstSinkhornCovariance.columnPotential
    (transpose L) logColumns logRows initialColumn k

theorem columnPotential_zero (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) :
    columnPotential L logRows logColumns initialColumn 0 = initialColumn := rfl

theorem rowPotential_update (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) :
    rowPotential L logRows logColumns initialColumn k =
      ColumnFirstSinkhornCovariance.rowUpdate L logRows
        (columnPotential L logRows logColumns initialColumn k) := rfl

theorem columnPotential_succ (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) :
    columnPotential L logRows logColumns initialColumn (k+1) =
      ColumnFirstSinkhornCovariance.columnUpdate L logColumns
        (rowPotential L logRows logColumns initialColumn k) := rfl

def halfLogPlan (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) : I → J → ℝ :=
  transpose (ColumnFirstSinkhornCovariance.halfLogPlan
    (transpose L) logColumns logRows initialColumn k)

def fullLogPlan (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) : I → J → ℝ :=
  transpose (ColumnFirstSinkhornCovariance.fullLogPlan
    (transpose L) logColumns logRows initialColumn k)

variable [Nonempty I] [Nonempty J]

theorem columnPotential_rowShift (L : I → J → ℝ) (d logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) :
    columnPotential (rowShift L d) logRows logColumns initialColumn k =
      columnPotential L logRows logColumns initialColumn k := by
  unfold columnPotential
  rw [transpose_rowShift, ColumnFirstSinkhornCovariance.rowPotential_columnShift]

theorem rowPotential_rowShift (L : I → J → ℝ) (d logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) :
    rowPotential (rowShift L d) logRows logColumns initialColumn k =
      fun i => rowPotential L logRows logColumns initialColumn k i - d i := by
  unfold rowPotential
  rw [transpose_rowShift, ColumnFirstSinkhornCovariance.columnPotential_columnShift]

theorem halfLogPlan_rowShift (L : I → J → ℝ) (d logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) :
    halfLogPlan (rowShift L d) logRows logColumns initialColumn k =
      halfLogPlan L logRows logColumns initialColumn k := by
  unfold halfLogPlan
  rw [transpose_rowShift, ColumnFirstSinkhornCovariance.halfLogPlan_columnShift]

theorem fullLogPlan_rowShift (L : I → J → ℝ) (d logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) :
    fullLogPlan (rowShift L d) logRows logColumns initialColumn k =
      fullLogPlan L logRows logColumns initialColumn k := by
  unfold fullLogPlan
  rw [transpose_rowShift, ColumnFirstSinkhornCovariance.fullLogPlan_columnShift]

theorem halfPlan_rowShift (L : I → J → ℝ) (d logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) (i : I) (j : J) :
    Real.exp (halfLogPlan (rowShift L d) logRows logColumns initialColumn k i j) =
      Real.exp (halfLogPlan L logRows logColumns initialColumn k i j) := by
  rw [halfLogPlan_rowShift]

theorem fullPlan_rowShift (L : I → J → ℝ) (d logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) (i : I) (j : J) :
    Real.exp (fullLogPlan (rowShift L d) logRows logColumns initialColumn k i j) =
      Real.exp (fullLogPlan L logRows logColumns initialColumn k i j) := by
  rw [fullLogPlan_rowShift]

theorem halfPlan_row_normalization (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) (i : I) :
    (∑ j, Real.exp (halfLogPlan L logRows logColumns initialColumn k i j)) =
      Real.exp (logRows i) := by
  exact ColumnFirstSinkhornCovariance.columnUpdate_normalizes (transpose L) logRows
    (ColumnFirstSinkhornCovariance.rowPotential
      (transpose L) logColumns logRows initialColumn k) i

theorem fullPlan_column_normalization (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns initialColumn : J → ℝ) (k : ℕ) (j : J) :
    (∑ i, Real.exp (fullLogPlan L logRows logColumns initialColumn k i j)) =
      Real.exp (logColumns j) := by
  have h := ColumnFirstSinkhornCovariance.rowUpdate_normalizes (transpose L) logColumns
    (ColumnFirstSinkhornCovariance.columnPotential
      (transpose L) logColumns logRows initialColumn k) j
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold fullLogPlan transpose ColumnFirstSinkhornCovariance.fullLogPlan
    ColumnFirstSinkhornCovariance.columnPotential ColumnFirstSinkhornCovariance.rowPotential
  ring

end
end InfoGeometry.Spectrometry.SpectralOrientation

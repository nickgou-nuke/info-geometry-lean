/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exact covariance of column-first log-domain Sinkhorn iterations

Verified with Lean 4.34.1 and Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`; see the verification log.

The targets are supplied as log margins. Row and column index types are
finite and nonempty. Both runs use the same initial row potential and the
same target margins. There is no extra gauge normalization of potentials.

`columnPotential ... k` is the column update from `rowPotential ... k`.
Thus k = 0 already denotes the first column update; the corresponding full
iteration finishes with `rowPotential ... (k+1)`. No convergence theorem is
needed for covariance at any of these finite steps. This theorem does not
identify a column-first trajectory with a row-first trajectory.
-/

namespace InfoGeometry.Spectrometry.ColumnFirstSinkhornCovariance

open scoped BigOperators

noncomputable section

def logSumExp {K : Type*} [Fintype K] (f : K → ℝ) : ℝ :=
  Real.log (∑ k, Real.exp (f k))

theorem exp_sum_pos {K : Type*} [Fintype K] [Nonempty K] (f : K → ℝ) :
    0 < ∑ k, Real.exp (f k) := by
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem logSumExp_add_const {K : Type*} [Fintype K] [Nonempty K]
    (f : K → ℝ) (c : ℝ) :
    logSumExp (fun k => f k + c) = logSumExp f + c := by
  have hsum : (∑ k, Real.exp (f k + c)) =
      (∑ k, Real.exp (f k)) * Real.exp c := by
    simp only [Real.exp_add, Finset.sum_mul]
  unfold logSumExp
  rw [hsum, Real.log_mul (exp_sum_pos f).ne' (Real.exp_ne_zero c), Real.log_exp]

theorem exp_normalization {K : Type*} [Fintype K] [Nonempty K]
    (f : K → ℝ) (c : ℝ) :
    (∑ k, Real.exp (f k + (c - logSumExp f))) = Real.exp c := by
  calc
    (∑ k, Real.exp (f k + (c - logSumExp f))) =
        (∑ k, Real.exp (f k)) * Real.exp (c - logSumExp f) := by
      simp only [Real.exp_add, Finset.sum_mul]
    _ = (∑ k, Real.exp (f k)) * (Real.exp c / ∑ k, Real.exp (f k)) := by
      rw [Real.exp_sub, logSumExp, Real.exp_log (exp_sum_pos f)]
    _ = Real.exp c := by
      field_simp [(exp_sum_pos f).ne']

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

def columnShift (L : I → J → ℝ) (d : J → ℝ) : I → J → ℝ :=
  fun i j => L i j + d j

def rowUpdate (L : I → J → ℝ) (logRows : I → ℝ) (beta : J → ℝ) : I → ℝ :=
  fun i => logRows i - logSumExp (fun j => L i j + beta j)

def columnUpdate (L : I → J → ℝ) (logColumns : J → ℝ)
    (alpha : I → ℝ) : J → ℝ :=
  fun j => logColumns j - logSumExp (fun i => L i j + alpha i)

theorem columnUpdate_columnShift (L : I → J → ℝ) (d logColumns : J → ℝ)
    (alpha : I → ℝ) :
    columnUpdate (columnShift L d) logColumns alpha =
      fun j => columnUpdate L logColumns alpha j - d j := by
  funext j
  change logColumns j - logSumExp (fun i => (L i j + d j) + alpha i) =
    (logColumns j - logSumExp (fun i => L i j + alpha i)) - d j
  have hfun : (fun i => (L i j + d j) + alpha i) =
      (fun i => (L i j + alpha i) + d j) := by
    funext i
    ring
  rw [hfun, logSumExp_add_const]
  ring

theorem rowUpdate_columnShift (L : I → J → ℝ) (d beta : J → ℝ)
    (logRows : I → ℝ) :
    rowUpdate (columnShift L d) logRows (fun j => beta j - d j) =
      rowUpdate L logRows beta := by
  funext i
  change logRows i - logSumExp (fun j => (L i j + d j) + (beta j - d j)) =
    logRows i - logSumExp (fun j => L i j + beta j)
  congr 1
  congr 1
  funext j
  ring

/-- The column update really imposes the supplied positive column margin. -/
theorem columnUpdate_normalizes (L : I → J → ℝ) (logColumns : J → ℝ)
    (alpha : I → ℝ) (j : J) :
    (∑ i, Real.exp (L i j + alpha i + columnUpdate L logColumns alpha j)) =
      Real.exp (logColumns j) := by
  simpa only [columnUpdate] using
    exp_normalization (fun i => L i j + alpha i) (logColumns j)

/-- The row update really imposes the supplied positive row margin. -/
theorem rowUpdate_normalizes (L : I → J → ℝ) (logRows : I → ℝ)
    (beta : J → ℝ) (i : I) :
    (∑ j, Real.exp (L i j + beta j + rowUpdate L logRows beta i)) =
      Real.exp (logRows i) := by
  simpa only [rowUpdate] using
    exp_normalization (fun j => L i j + beta j) (logRows i)

def rowPotential (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns : J → ℝ) (initial : I → ℝ) : ℕ → I → ℝ :=
  Nat.rec initial (fun _ alpha =>
    rowUpdate L logRows (columnUpdate L logColumns alpha))

def columnPotential (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ) : J → ℝ :=
  columnUpdate L logColumns (rowPotential L logRows logColumns initial k)

theorem rowPotential_columnShift (L : I → J → ℝ) (d : J → ℝ)
    (logRows : I → ℝ) (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ) :
    rowPotential (columnShift L d) logRows logColumns initial k =
      rowPotential L logRows logColumns initial k := by
  induction k with
  | zero => rfl
  | succ k hk =>
      change rowUpdate (columnShift L d) logRows
        (columnUpdate (columnShift L d) logColumns
          (rowPotential (columnShift L d) logRows logColumns initial k)) =
        rowUpdate L logRows
          (columnUpdate L logColumns (rowPotential L logRows logColumns initial k))
      rw [hk, columnUpdate_columnShift, rowUpdate_columnShift]

theorem columnPotential_columnShift (L : I → J → ℝ) (d : J → ℝ)
    (logRows : I → ℝ) (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ) :
    columnPotential (columnShift L d) logRows logColumns initial k =
      fun j => columnPotential L logRows logColumns initial k j - d j := by
  unfold columnPotential
  rw [rowPotential_columnShift, columnUpdate_columnShift]

def halfLogPlan (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ) : I → J → ℝ :=
  fun i j => L i j + rowPotential L logRows logColumns initial k i +
    columnPotential L logRows logColumns initial k j

def fullLogPlan (L : I → J → ℝ) (logRows : I → ℝ)
    (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ) : I → J → ℝ :=
  fun i j => L i j + rowPotential L logRows logColumns initial (k+1) i +
    columnPotential L logRows logColumns initial k j

theorem halfLogPlan_columnShift (L : I → J → ℝ) (d : J → ℝ)
    (logRows : I → ℝ) (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ) :
    halfLogPlan (columnShift L d) logRows logColumns initial k =
      halfLogPlan L logRows logColumns initial k := by
  funext i j
  simp only [halfLogPlan, rowPotential_columnShift, columnPotential_columnShift,
    columnShift]
  ring

theorem fullLogPlan_columnShift (L : I → J → ℝ) (d : J → ℝ)
    (logRows : I → ℝ) (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ) :
    fullLogPlan (columnShift L d) logRows logColumns initial k =
      fullLogPlan L logRows logColumns initial k := by
  funext i j
  simp only [fullLogPlan, rowPotential_columnShift, columnPotential_columnShift,
    columnShift]
  ring

theorem halfPlan_columnShift (L : I → J → ℝ) (d : J → ℝ)
    (logRows : I → ℝ) (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ)
    (i : I) (j : J) :
    Real.exp (halfLogPlan (columnShift L d) logRows logColumns initial k i j) =
      Real.exp (halfLogPlan L logRows logColumns initial k i j) := by
  rw [halfLogPlan_columnShift]

theorem fullPlan_columnShift (L : I → J → ℝ) (d : J → ℝ)
    (logRows : I → ℝ) (logColumns : J → ℝ) (initial : I → ℝ) (k : ℕ)
    (i : I) (j : J) :
    Real.exp (fullLogPlan (columnShift L d) logRows logColumns initial k i j) =
      Real.exp (fullLogPlan L logRows logColumns initial k i j) := by
  rw [fullLogPlan_columnShift]

end
end InfoGeometry.Spectrometry.ColumnFirstSinkhornCovariance

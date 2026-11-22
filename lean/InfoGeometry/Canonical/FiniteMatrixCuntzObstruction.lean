/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.Cuntz2Isometries
import InfoGeometry.Canonical.FiniteCantorBranchAmplification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.NCG.CuntzColimitKMSTiltGNS
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Finite-dimensional obstruction for Cuntz O₂ generators

The normalized matrix trace tower is a genuine noncommutative UHF tower, but
it cannot itself be a stagewise `Cuntz2Isometries` tower: two isometries with
orthogonal ranges would force `2 * dim = dim`.  This theorem records that
trace obstruction explicitly, preventing an invalid concrete Cuntz
instantiation at finite matrix stages.

The constructive finite replacement is the existing rectangular branch system.
`FiniteCantorCuntzBranches.amplify` refines arbitrary endomorphisms between
successive word stages, preserves identity and composition, is injective,
and intertwines the diagonal bonding map on vectors.
-/

namespace InfoGeometry.Canonical.FiniteMatrixCuntzObstruction

open CuntzAlgebra

theorem no_cuntz2_matrix {n : ℕ} (hn : 0 < n)
    (C : Cuntz2Isometries (Matrix (Fin n) (Fin n) ℂ)) : False := by
  have h₁ : Matrix.trace (CuntzAlgebra.S1 C * star (CuntzAlgebra.S1 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry1 C, Matrix.trace_one]
    simp
  have h₂ : Matrix.trace (CuntzAlgebra.S2 C * star (CuntzAlgebra.S2 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry2 C, Matrix.trace_one]
    simp
  have hsum := congrArg Matrix.trace (CuntzAlgebra.h_range_sum C)
  rw [Matrix.trace_add, h₁, h₂, Matrix.trace_one] at hsum
  have hnat' : n + n = Fintype.card (Fin n) := by
    exact_mod_cast hsum
  have hnat : n + n = n := by
    simpa using hnat'
  omega

/-- The finite trace balance for a Cuntz₂ pair forces the matrix dimension to
vanish. This is the exact numerical obstruction behind the positive-dimension
no-go theorem. -/
theorem cuntz2_matrix_dimension_eq_zero {n : ℕ}
    (C : Cuntz2Isometries (Matrix (Fin n) (Fin n) ℂ)) : n = 0 := by
  have h₁ : Matrix.trace (CuntzAlgebra.S1 C * star (CuntzAlgebra.S1 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry1 C, Matrix.trace_one]
    simp
  have h₂ : Matrix.trace (CuntzAlgebra.S2 C * star (CuntzAlgebra.S2 C)) = (n : ℂ) := by
    rw [Matrix.trace_mul_comm, CuntzAlgebra.h_isometry2 C, Matrix.trace_one]
    simp
  have hsum := congrArg Matrix.trace (CuntzAlgebra.h_range_sum C)
  rw [Matrix.trace_add, h₁, h₂, Matrix.trace_one] at hsum
  have hnat' : n + n = Fintype.card (Fin n) := by
    exact_mod_cast hsum
  have hnat : n + n = n := by
    simpa using hnat'
  omega

/-- Each range projection of a finite Cuntz family in a square complex
matrix algebra has trace equal to the ambient matrix dimension. -/
theorem cuntz_range_projection_trace_eq_dimension
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : InfoGeometry.NCG.CuntzSystem ι (Matrix (Fin n) (Fin n) ℂ))
    (i : ι) :
    Matrix.trace (C.S i * star (C.S i)) = (n : ℂ) := by
  have hisometry : star (C.S i) * C.S i = 1 := by
    simpa using C.isometry' i i
  rw [Matrix.trace_mul_comm, hisometry, Matrix.trace_one]
  simp

/-- Trace balance for a finite Cuntz family in a square complex matrix
algebra. Each range projection has trace equal to the matrix dimension, while
their sum is the identity. -/
theorem finite_matrix_cuntz_trace_balance
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : InfoGeometry.NCG.CuntzSystem ι (Matrix (Fin n) (Fin n) ℂ)) :
    (Fintype.card ι : ℂ) * (n : ℂ) = (n : ℂ) := by
  have htrace := congrArg Matrix.trace C.completeness'
  rw [Matrix.trace_sum] at htrace
  simp_rw [cuntz_range_projection_trace_eq_dimension C] at htrace
  rw [Matrix.trace_one] at htrace
  simpa using htrace

/-- A finite-dimensional complex matrix algebra cannot carry a complete Cuntz
family with at least two generators. The proof is the trace balance for the
actual range projections of the generic `CuntzSystem` owner. -/
theorem finite_matrix_cuntz_system_dimension_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hcard : 2 ≤ Fintype.card ι)
    (C : InfoGeometry.NCG.CuntzSystem ι (Matrix (Fin n) (Fin n) ℂ)) : n = 0 := by
  have hcard_mul : (Fintype.card ι : ℂ) * (n : ℂ) = (n : ℂ) := by
    exact finite_matrix_cuntz_trace_balance C
  have hcard_gt : 1 < Fintype.card ι := by omega
  have hcoeff : (Fintype.card ι : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt hcard_gt)
  have hzero : ((Fintype.card ι : ℂ) - 1) * (n : ℂ) = 0 := by
    calc
      ((Fintype.card ι : ℂ) - 1) * (n : ℂ) =
          (Fintype.card ι : ℂ) * (n : ℂ) - (n : ℂ) := by ring
      _ = 0 := by rw [hcard_mul]; ring
  rcases mul_eq_zero.mp hzero with h | h
  · exact (hcoeff h).elim
  · exact_mod_cast h

/-- Exact finite-dimensional boundary for a generic Cuntz family: in positive
matrix dimension its index must be a singleton. Thus the obstruction theorem
for two or more generators is the non-singleton half of this classification. -/
theorem finite_matrix_cuntz_system_dimension_or_single_generator
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : InfoGeometry.NCG.CuntzSystem ι (Matrix (Fin n) (Fin n) ℂ)) :
    n = 0 ∨ Fintype.card ι = 1 := by
  by_cases hzero : n = 0
  · exact Or.inl hzero
  · right
    have hn : 0 < n := Nat.pos_of_ne_zero hzero
    have hnat : Fintype.card ι * n = n := by
      exact_mod_cast finite_matrix_cuntz_trace_balance C
    have hmul : n * Fintype.card ι = n * 1 := by
      simpa [Nat.mul_comm] using hnat
    exact Nat.eq_of_mul_eq_mul_left hn hmul

theorem no_finite_matrix_cuntz_system {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 0 < n) (hcard : 2 ≤ Fintype.card ι)
    (C : InfoGeometry.NCG.CuntzSystem ι (Matrix (Fin n) (Fin n) ℂ)) : False := by
  have hdim := finite_matrix_cuntz_system_dimension_eq_zero hcard C
  omega

end InfoGeometry.Canonical.FiniteMatrixCuntzObstruction

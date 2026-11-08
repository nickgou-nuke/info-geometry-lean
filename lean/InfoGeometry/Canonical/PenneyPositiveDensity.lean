/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PenneyLeftCovariance
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Penney: positive scalar trace readout and temporal conservation

The squared-entry readout is a finite-dimensional real Hilbert--Schmidt
quantity `Matrix.trace (xᵀ * x)`. It is a *positive scalar* analogue of
Penney's traced density, accompanied by constructive sectorwise positivity
and skew-adjoint `wheelJ` matrix Gram conservation on `SplitQuaternion ℝ`.
-/
namespace InfoGeometry.Canonical.PenneyPositiveDensity

open scoped Matrix
open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {n : Type*} [Fintype n]

/-- Finite nonnegative sum of squared real matrix coefficients. -/
def squaredEntryTrace (x : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, (x i j) ^ 2

/-- The Hilbert–Schmidt Gram trace `Matrix.trace (xᵀ * x)` equals `squaredEntryTrace x`. -/
theorem trace_transpose_mul_self_eq_squaredEntryTrace (x : Matrix n n ℝ) :
    Matrix.trace (xᵀ * x) = squaredEntryTrace x := by
  unfold squaredEntryTrace
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

/-- The scalar trace-of-squares readout cannot be negative. -/
theorem squaredEntryTrace_nonneg (x : Matrix n n ℝ) :
    0 ≤ squaredEntryTrace x := by
  unfold squaredEntryTrace
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact sq_nonneg (x i j)

/-- Zero-hypothesis nonnegativity of the matrix Gram trace `Matrix.trace (xᵀ * x)`. -/
theorem trace_transpose_mul_self_nonneg (x : Matrix n n ℝ) :
    0 ≤ Matrix.trace (xᵀ * x) := by
  rw [trace_transpose_mul_self_eq_squaredEntryTrace]
  exact squaredEntryTrace_nonneg x

/-- Positive density of a pair of real matrix-valued fields. -/
def pairedDensity (χ φ : Matrix n n ℝ) : ℝ :=
  squaredEntryTrace χ + squaredEntryTrace φ

theorem pairedDensity_nonneg (χ φ : Matrix n n ℝ) :
    0 ≤ pairedDensity χ φ :=
  add_nonneg (squaredEntryTrace_nonneg χ) (squaredEntryTrace_nonneg φ)

/-- Zero-hypothesis right-isospin sectorwise Gram trace nonnegativity on `SplitQuaternion ℝ`. -/
theorem splitQuaternion_sector_gram_trace_nonneg (χ : SplitQuaternion ℝ) :
    0 ≤ Matrix.trace (star (χ * peircePlus) * (χ * peircePlus)) ∧
    0 ≤ Matrix.trace (star (χ * peirceMinus) * (χ * peirceMinus)) ∧
    0 ≤ Matrix.trace (star χ * χ) :=
  ⟨trace_star_mul_self_peircePlus_nonneg χ,
   trace_star_mul_self_peirceMinus_nonneg χ,
   trace_star_mul_self_nonneg χ⟩

/-- Zero-hypothesis exact `2 × 2` matrix Gram conservation under the skew-adjoint generator `wheelJ`. -/
theorem splitQuaternion_wheelJ_gram_conservation (χ : SplitQuaternion ℝ) :
    star (wheelJ * χ) * χ + star χ * (wheelJ * χ) = 0 ∧
    star ((wheelJ * χ) * peircePlus) * (χ * peircePlus) +
      star (χ * peircePlus) * ((wheelJ * χ) * peircePlus) = 0 ∧
    star ((wheelJ * χ) * peirceMinus) * (χ * peirceMinus) +
      star (χ * peirceMinus) * ((wheelJ * χ) * peirceMinus) = 0 :=
  ⟨wheelJ_gram_deriv_zero χ,
   (wheelJ_peirce_sector_gram_deriv_zero χ).1,
   (wheelJ_peirce_sector_gram_deriv_zero χ).2⟩

/-- Real two-amplitude analogue of one right-isospin column's density. -/
def temporalDensity (χ φ : ℝ) : ℝ := χ * χ + φ * φ

theorem temporalDensity_nonneg (χ φ : ℝ) :
    0 ≤ temporalDensity χ φ :=
  add_nonneg (mul_self_nonneg χ) (mul_self_nonneg φ)

/-- A first-order antisymmetric evolution conserves the density.
    This is an explicit ODE result, not the full Penney continuity PDE. -/
theorem temporalDensity_hasDerivAt_zero
    (χ φ : ℝ → ℝ) (a t : ℝ)
    (hχ : HasDerivAt χ (a * φ t) t)
    (hφ : HasDerivAt φ (-(a * χ t)) t) :
    HasDerivAt (fun s => temporalDensity (χ s) (φ s)) 0 t := by
  have hsum :
      HasDerivAt (fun s => temporalDensity (χ s) (φ s))
        ((a * φ t) * χ t + χ t * (a * φ t) +
          (-(a * χ t) * φ t + φ t * -(a * χ t))) t :=
    (hχ.mul hχ).add (hφ.mul hφ)
  have hzero :
      (a * φ t) * χ t + χ t * (a * φ t) +
        (-(a * χ t) * φ t + φ t * -(a * χ t)) = 0 := by ring
  rwa [hzero] at hsum

end InfoGeometry.Canonical.PenneyPositiveDensity

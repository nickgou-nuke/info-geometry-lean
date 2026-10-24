/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PenneyLeftCovariance
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Penney: positive scalar trace readout and temporal conservation

The squared-entry readout is a finite-dimensional real Hilbert--Schmidt
quantity. It is a *positive scalar* analogue of Penney's traced density,
not a proof of positivity of the quaternion-valued density itself.

The oscillator result proves temporal conservation for an explicit system.
A spacetime divergence identity still needs a spatial PDE and current.
-/
namespace InfoGeometry.Canonical.PenneyPositiveDensity

variable {n : Type*} [Fintype n]

/-- Finite nonnegative sum of squared real matrix coefficients. -/
def squaredEntryTrace (x : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, (x i j) ^ 2

/-- The scalar trace-of-squares readout cannot be negative. -/
theorem squaredEntryTrace_nonneg (x : Matrix n n ℝ) :
    0 ≤ squaredEntryTrace x := by
  unfold squaredEntryTrace
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact sq_nonneg (x i j)

/-- Positive density of a pair of real matrix-valued fields. -/
def pairedDensity (χ φ : Matrix n n ℝ) : ℝ :=
  squaredEntryTrace χ + squaredEntryTrace φ

theorem pairedDensity_nonneg (χ φ : Matrix n n ℝ) :
    0 ≤ pairedDensity χ φ :=
  add_nonneg (squaredEntryTrace_nonneg χ) (squaredEntryTrace_nonneg φ)

/-- Real two-amplitude analogue of one right-isospin column's density. -/
def temporalDensity (χ φ : ℝ) : ℝ := χ * χ + φ * φ

theorem temporalDensity_nonneg (χ φ : ℝ) :
    0 ≤ temporalDensity χ φ := by
  unfold temporalDensity
  positivity

/-- A first-order antisymmetric evolution conserves the density.
    This is an explicit ODE result, not the full Penney continuity PDE. -/
theorem temporalDensity_hasDerivAt_zero
    (χ φ : ℝ → ℝ) (a t : ℝ)
    (hχ : HasDerivAt χ (a * φ t) t)
    (hφ : HasDerivAt φ (-(a * χ t)) t) :
    HasDerivAt (fun s => temporalDensity (χ s) (φ s)) 0 t := by
  have hχsq := hχ.mul hχ
  have hφsq := hφ.mul hφ
  have hsum := hχsq.add hφsq
  convert hsum using 1 <;> simp only [temporalDensity] <;> ring

end InfoGeometry.Canonical.PenneyPositiveDensity

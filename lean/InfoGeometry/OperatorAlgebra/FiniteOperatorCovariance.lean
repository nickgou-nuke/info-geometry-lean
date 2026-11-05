/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CovarianceTransport
import Mathlib.Algebra.Star.Module

/-!
# Exact finite weighted operator covariance

Samples are full elements of a real star algebra. Their cross covariance keeps
its operator value and the orientation `X° * star Y°`. Normalized nonnegative
weights give a finite probability ensemble. Algebraic linearity needs neither
nonnegativity nor normalization; invariance under deterministic offsets uses
normalization explicitly, and matrix positivity uses nonnegative weights.

The innovation closure is an exact consequence of zero centered cross
covariance. Independence, conditional expectations, large-dimension limits,
and the scalar gain formula from the motivating article are not asserted.
-/

namespace InfoGeometry.OperatorAlgebra.FiniteOperatorCovariance

open scoped BigOperators
open InfoGeometry.OperatorAlgebra.CovarianceTransport

variable {Ω A : Type*} [Fintype Ω] [Ring A] [Algebra ℝ A]

/-- Finite weighted mean, still valued in the full operator algebra. -/
def mean (w : Ω → ℝ) (X : Ω → A) : A := ∑ ω, w ω • X ω

/-- Centering subtracts the operator mean rather than a scalar trace readout. -/
def centered (w : Ω → ℝ) (X : Ω → A) (ω : Ω) : A := X ω - mean w X

theorem mean_add (w : Ω → ℝ) (X Y : Ω → A) :
    mean w (fun ω => X ω + Y ω) = mean w X + mean w Y := by
  simp only [mean, smul_add, Finset.sum_add_distrib]

theorem mean_sub (w : Ω → ℝ) (X Y : Ω → A) :
    mean w (fun ω => X ω - Y ω) = mean w X - mean w Y := by
  simp only [mean, smul_sub, Finset.sum_sub_distrib]

theorem mean_const (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (B : A) :
    mean w (fun _ => B) = B := by
  rw [mean, ← Finset.sum_smul, hw, one_smul]

theorem mean_left_mul (w : Ω → ℝ) (T : A) (X : Ω → A) :
    mean w (fun ω => T * X ω) = T * mean w X := by
  simp only [mean, Finset.mul_sum, mul_smul_comm]

theorem mean_right_mul (w : Ω → ℝ) (T : A) (X : Ω → A) :
    mean w (fun ω => X ω * T) = mean w X * T := by
  simp only [mean, Finset.sum_mul, smul_mul_assoc]

/-- Deterministic affine transport commutes with the normalized operator mean. -/
theorem mean_affine (w : Ω → ℝ) (hw : ∑ ω, w ω = 1)
    (T B : A) (X : Ω → A) :
    mean w (fun ω => T * X ω + B) = T * mean w X + B := by
  rw [mean_add, mean_left_mul, mean_const w hw]

theorem centered_add (w : Ω → ℝ) (X Y : Ω → A) (ω : Ω) :
    centered w (fun ω => X ω + Y ω) ω = centered w X ω + centered w Y ω := by
  simp only [centered, mean_add]
  abel

theorem centered_left_mul (w : Ω → ℝ) (T : A) (X : Ω → A) (ω : Ω) :
    centered w (fun ω => T * X ω) ω = T * centered w X ω := by
  simp only [centered, mean_left_mul, mul_sub]

theorem centered_affine (w : Ω → ℝ) (hw : ∑ ω, w ω = 1)
    (T B : A) (X : Ω → A) (ω : Ω) :
    centered w (fun ω => T * X ω + B) ω = T * centered w X ω := by
  simp only [centered, mean_affine w hw]
  noncomm_ring

/-- Centered samples have zero weighted operator mean. -/
theorem mean_centered (w : Ω → ℝ) (hw : ∑ ω, w ω = 1) (X : Ω → A) :
    mean w (centered w X) = 0 := by
  change mean w (fun ω => X ω - mean w X) = 0
  rw [mean_sub, mean_const w hw, sub_self]

variable [StarRing A]

/-- Oriented operator-valued cross covariance. -/
def crossCovariance (w : Ω → ℝ) (X Y : Ω → A) : A :=
  mean w (fun ω => centered w X ω * star (centered w Y ω))

theorem crossCovariance_add_left (w : Ω → ℝ) (X Y Z : Ω → A) :
    crossCovariance w (fun ω => X ω + Y ω) Z =
      crossCovariance w X Z + crossCovariance w Y Z := by
  simp only [crossCovariance, centered_add, add_mul, mean_add]

theorem crossCovariance_add_right (w : Ω → ℝ) (X Y Z : Ω → A) :
    crossCovariance w X (fun ω => Y ω + Z ω) =
      crossCovariance w X Y + crossCovariance w X Z := by
  simp only [crossCovariance, centered_add, star_add, mul_add, mean_add]

theorem crossCovariance_left_mul (w : Ω → ℝ) (T : A) (X Y : Ω → A) :
    crossCovariance w (fun ω => T * X ω) Y = T * crossCovariance w X Y := by
  simp only [crossCovariance, centered_left_mul, mul_assoc, mean_left_mul]

theorem crossCovariance_right_mul (w : Ω → ℝ) (T : A) (X Y : Ω → A) :
    crossCovariance w X (fun ω => T * Y ω) = crossCovariance w X Y * star T := by
  simp only [crossCovariance, centered_left_mul, star_mul, ← mul_assoc, mean_right_mul]

/-- Full two-sided covariance transport under deterministic affine changes. -/
theorem crossCovariance_affine (w : Ω → ℝ) (hw : ∑ ω, w ω = 1)
    (T B S D : A) (X Y : Ω → A) :
    crossCovariance w (fun ω => T * X ω + B) (fun ω => S * Y ω + D) =
      T * crossCovariance w X Y * star S := by
  simp only [crossCovariance, centered_affine w hw, mean, star_mul,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]

variable [StarModule ℝ A]

theorem mean_star (w : Ω → ℝ) (X : Ω → A) :
    mean w (fun ω => star (X ω)) = star (mean w X) := by
  simp only [mean, star_sum, star_smul, star_trivial]

/-- The normalized centered cross covariance is the raw moment minus the mean product. -/
theorem crossCovariance_eq_secondMoment_sub (w : Ω → ℝ) (hw : ∑ ω, w ω = 1)
    (X Y : Ω → A) :
    crossCovariance w X Y =
      mean w (fun ω => X ω * star (Y ω)) - mean w X * star (mean w Y) := by
  simp only [crossCovariance, centered, star_sub, sub_mul, mul_sub, mean_sub,
    mean_left_mul, mean_right_mul, mean_const w hw, mean_star]
  abel

/-- Exact mean-plus-fluctuation decomposition before any trace is taken. -/
theorem secondMoment_eq_covariance_add_mean (w : Ω → ℝ) (hw : ∑ ω, w ω = 1)
    (X : Ω → A) :
    mean w (fun ω => X ω * star (X ω)) =
      crossCovariance w X X + mean w X * star (mean w X) := by
  exact (sub_eq_iff_eq_add).1 (crossCovariance_eq_secondMoment_sub w hw X X).symm

/-- Swapping the samples takes the adjoint, not an unrestricted equality. -/
theorem crossCovariance_star (w : Ω → ℝ) (X Y : Ω → A) :
    star (crossCovariance w X Y) = crossCovariance w Y X := by
  simp only [crossCovariance, mean, star_sum, star_smul, star_trivial, star_mul, star_star]

/-- The exact innovation formula retains both mixed covariance operators. -/
theorem innovation_covariance (w : Ω → ℝ) (T : A) (X E : Ω → A) :
    crossCovariance w (fun ω => T * X ω + E ω) (fun ω => T * X ω + E ω) =
      covarianceStep T (crossCovariance w E E) (crossCovariance w X X) +
        T * crossCovariance w X E + star (crossCovariance w X E) * star T := by
  simp only [crossCovariance_add_left, crossCovariance_add_right,
    crossCovariance_left_mul, crossCovariance_right_mul, covarianceStep, crossCovariance_star]
  noncomm_ring

/-- The directed lag keeps the orientation of the mixed covariance. -/
theorem innovation_lag (w : Ω → ℝ) (T : A) (X E : Ω → A) :
    crossCovariance w (fun ω => T * X ω + E ω) X =
      T * crossCovariance w X X + star (crossCovariance w X E) := by
  simp only [crossCovariance_add_left, crossCovariance_left_mul, crossCovariance_star]

/-- Zero centered cross covariance is an explicit sufficient closure hypothesis. -/
theorem innovation_covariance_of_cross_zero (w : Ω → ℝ) (T : A) (X E : Ω → A)
    (hXE : crossCovariance w X E = 0) :
    crossCovariance w (fun ω => T * X ω + E ω) (fun ω => T * X ω + E ω) =
      covarianceStep T (crossCovariance w E E) (crossCovariance w X X) := by
  rw [innovation_covariance, hXE]
  simp only [mul_zero, star_zero, zero_mul, add_zero]

theorem innovation_lag_of_cross_zero (w : Ω → ℝ) (T : A) (X E : Ω → A)
    (hXE : crossCovariance w X E = 0) :
    crossCovariance w (fun ω => T * X ω + E ω) X = T * crossCovariance w X X := by
  rw [innovation_lag, hXE, star_zero, add_zero]

section Matrices

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Nonnegative weights make the full matrix covariance positive semidefinite. -/
theorem covariance_posSemidef (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (X : Ω → Matrix n n ℂ) : (crossCovariance w X X).PosSemidef := by
  classical
  have hterm (ω : Ω) :
      (w ω • (centered w X ω * star (centered w X ω))).PosSemidef := by
    exact (Matrix.posSemidef_self_mul_conjTranspose (centered w X ω)).smul (hw ω)
  unfold crossCovariance mean
  induction (Finset.univ : Finset Ω) using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  | @insert ω s hω ih =>
      rw [Finset.sum_insert hω]
      exact (hterm ω).add ih

end Matrices

end InfoGeometry.OperatorAlgebra.FiniteOperatorCovariance

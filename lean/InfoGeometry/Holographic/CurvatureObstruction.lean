/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.RealMatrixSplit
import Mathlib.Tactic.Linarith

/-!
# Skew curvature and the obstruction to a symmetric metric correction

Equation (30) of the holographic white paper v6.1 defines an antisymmetric
finite-difference field. A finite weighted sum remains antisymmetric. Thus
equation (31), `eta + kappa • H`, is symmetric only if its skew correction
vanishes. Native real self/skew adjoint parts identify the two components.

Only finite sums are constructed; an infinite prime sum needs a separate
summability proof. Symmetry is not a proof of nondegeneracy or signature.
-/

noncomputable section

namespace InfoGeometry.Holographic.CurvatureObstruction

open Matrix InfoGeometry.OperatorAlgebra.RealMatrixSplit

variable {Direction Site : Type*}

/-- The finite-difference expression in equation (30); shifts are explicit data. -/
def fieldStrength (A : Direction → Site → ℝ) (shift : Direction → Site → Site)
    (p : Site) : Matrix Direction Direction ℝ :=
  fun i j => A j (shift i p) - A i (shift j p) - A j p + A i p

theorem fieldStrength_transpose (A : Direction → Site → ℝ)
    (shift : Direction → Site → Site) (p : Site) :
    (fieldStrength A shift p).transpose = -fieldStrength A shift p := by
  ext i j
  simp only [fieldStrength, Matrix.transpose_apply, Matrix.neg_apply]
  ring

/-- A cutoff is part of the mathematical data, not a convergence assertion. -/
def weightedCurvature (cutoff : Finset Site) (weight : Site → ℝ)
    (A : Direction → Site → ℝ) (shift : Direction → Site → Site) :
    Matrix Direction Direction ℝ :=
  ∑ p ∈ cutoff, weight p • fieldStrength A shift p

theorem weightedCurvature_transpose (cutoff : Finset Site) (weight : Site → ℝ)
    (A : Direction → Site → ℝ) (shift : Direction → Site → Site) :
    (weightedCurvature cutoff weight A shift).transpose =
      -weightedCurvature cutoff weight A shift := by
  simp only [weightedCurvature, Matrix.transpose_sum, Matrix.transpose_smul,
    fieldStrength_transpose, smul_neg, Finset.sum_neg_distrib]

variable {n : Type*}

/-- A nonzero skew correction cannot itself be a symmetric perturbation. -/
theorem symmetric_add_skew_iff_scaled_zero (eta H : Matrix n n ℝ)
    (heta : eta.transpose = eta) (hH : H.transpose = -H) (kappa : ℝ) :
    (eta + kappa • H).transpose = eta + kappa • H ↔ kappa • H = 0 := by
  constructor
  · intro h
    ext i j
    have he := congrArg (fun M : Matrix n n ℝ => M i j) heta
    have hh := congrArg (fun M : Matrix n n ℝ => M i j) hH
    have hg := congrArg (fun M : Matrix n n ℝ => M i j) h
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul] at he hh hg ⊢
    change kappa * H i j = 0
    rw [he, hh] at hg
    simp only [mul_neg] at hg
    linarith
  · intro h
    simp [h, heta]

theorem symmetric_add_skew_iff (eta H : Matrix n n ℝ)
    (heta : eta.transpose = eta) (hH : H.transpose = -H) (kappa : ℝ)
    (hkappa : kappa ≠ 0) :
    (eta + kappa • H).transpose = eta + kappa • H ↔ H = 0 := by
  rw [symmetric_add_skew_iff_scaled_zero eta H heta hH kappa,
    smul_eq_zero_iff_right hkappa]

/-- Native extraction of the symmetric component recovers only the background. -/
theorem selfAdjointPart_add_skew (eta H : Matrix n n ℝ)
    (heta : eta.transpose = eta) (hH : H.transpose = -H) (kappa : ℝ) :
    (selfAdjointPart ℝ (eta + kappa • H) : Matrix n n ℝ) = eta := by
  rw [selfAdjointPart_eq_half, Matrix.transpose_add, Matrix.transpose_smul, heta, hH]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  ring

/-- Native extraction of the skew component retains the entire curvature correction. -/
theorem skewAdjointPart_add_skew (eta H : Matrix n n ℝ)
    (heta : eta.transpose = eta) (hH : H.transpose = -H) (kappa : ℝ) :
    (skewAdjointPart ℝ (eta + kappa • H) : Matrix n n ℝ) = kappa • H := by
  rw [skewAdjointPart_eq_half, Matrix.transpose_add, Matrix.transpose_smul, heta, hH]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.neg_apply, smul_eq_mul]
  ring

/-- The source's finite-cutoff curvature obeys the same obstruction. -/
theorem weighted_curvature_metric_iff (cutoff : Finset Site) (weight : Site → ℝ)
    (A : Direction → Site → ℝ) (shift : Direction → Site → Site)
    (eta : Matrix Direction Direction ℝ) (heta : eta.transpose = eta)
    (kappa : ℝ) (hkappa : kappa ≠ 0) :
    (eta + kappa • weightedCurvature cutoff weight A shift).transpose =
      eta + kappa • weightedCurvature cutoff weight A shift ↔
      weightedCurvature cutoff weight A shift = 0 :=
  symmetric_add_skew_iff eta _ heta
    (weightedCurvature_transpose cutoff weight A shift) kappa hkappa

section OrderedProducts

variable [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A Gram correction is symmetric without requiring its factors to commute. -/
theorem gram_correction_symmetric (eta H : Matrix n n ℝ)
    (heta : eta.transpose = eta) (kappa : ℝ) :
    (eta + kappa • (H * H.transpose)).transpose = eta + kappa • (H * H.transpose) := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, heta]

/-- The nonsymmetric proposal retains the full ordered normality defect. -/
theorem skew_correction_normal_defect (eta H : Matrix n n ℝ)
    (heta : eta.transpose = eta) (hH : H.transpose = -H) (kappa : ℝ) :
    (eta + kappa • H).transpose * (eta + kappa • H) -
      (eta + kappa • H) * (eta + kappa • H).transpose =
      (2 * kappa) • (eta * H - H * eta) := by
  have hs : (kappa • H).transpose = -(kappa • H) := by
    simp [Matrix.transpose_smul, hH]
  rw [transpose_normal_defect_of_split heta hs rfl]
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_smul]

end OrderedProducts

end InfoGeometry.Holographic.CurvatureObstruction

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BesselHagenNoether
import Mathlib.Data.Matrix.Basic

/-!
# Real conformal stress currents

The current pairs a contravariant symmetric tensor with a covector. Its
divergence is the stress-divergence contraction plus the conformal factor
times the metric trace. The antisymmetric derivative contribution cancels
explicitly. No metric signature is silently replaced by a positive form.

The coordinate generators live in a commutative real differential algebra;
their coordinate and constant-coefficient hypotheses are stated explicitly.
No global group action, classification or integrated charge is asserted.
-/

noncomputable section

namespace InfoGeometry.Conformal.BesselHagenCurrent

open scoped BigOperators
open InfoGeometry.Canonical.BesselHagenNoether

variable {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι]

/-- Full tensor contraction, with the index positions supplied by the caller. -/
def contraction (S M : Matrix ι ι A) : A := ∑ i, ∑ j, S i j * M i j

/-- A contravariant stress tensor contracted with a covector. -/
def stressCurrent (S : Matrix ι ι A) (ξ : ι → A) (i : ι) : A :=
  ∑ j, S i j * ξ j

/-- Divergence in the first contravariant index. -/
def stressDivergence (D : ι → Derivation ℝ A A) (S : Matrix ι ι A) (j : ι) : A :=
  ∑ i, D i (S i j)

/-- The covector derivative matrix. -/
def covectorDerivative (D : ι → Derivation ℝ A A) (ξ : ι → A) : Matrix ι ι A :=
  fun i j => D i (ξ j)

/-- Algebraic conformal Killing equation for a covector and lower metric coefficients. -/
def IsConformalKilling (D : ι → Derivation ℝ A A) (g : Matrix ι ι A)
    (ξ : ι → A) (σ : A) : Prop :=
  ∀ i j, D i (ξ j) + D j (ξ i) = 2 * σ * g i j

omit [Algebra ℝ A] in
/-- A symmetric tensor cannot detect the skew part of another tensor. -/
theorem contraction_transpose (S M : Matrix ι ι A)
    (hS : ∀ i j, S i j = S j i) :
    contraction S M.transpose = contraction S M := by
  unfold contraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.transpose_apply, hS j i]

omit [Algebra ℝ A] in
/-- The symmetric and antisymmetric derivative sectors are separated explicitly. -/
theorem contraction_skew_part_zero (S M : Matrix ι ι A)
    (hS : ∀ i j, S i j = S j i) :
    contraction S (M - M.transpose) = 0 := by
  have h := contraction_transpose S M hS
  simpa only [contraction, Matrix.sub_apply, mul_sub,
    Finset.sum_sub_distrib, sub_eq_zero] using h.symm

/-- Exact contraction with the symmetric derivative sector. -/
theorem contraction_eq_half_symm (S M : Matrix ι ι A)
    (hS : ∀ i j, S i j = S j i) :
    contraction S M = (1 / 2 : ℝ) • contraction S (M + M.transpose) := by
  have hsum : contraction S (M + M.transpose) = contraction S M + contraction S M := by
    simp only [contraction, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    exact congrArg (fun a => contraction S M + a) (contraction_transpose S M hS)
  rw [hsum, smul_add, ← add_smul]
  norm_num

/-- Product rule for stress currents; no stress equations are assumed. -/
theorem divergence_stressCurrent (D : ι → Derivation ℝ A A)
    (S : Matrix ι ι A) (ξ : ι → A) :
    divergence D (stressCurrent S ξ) =
      (∑ j, stressDivergence D S j * ξ j) + contraction S (covectorDerivative D ξ) := by
  have hp i j : D i (S i j * ξ j) = D i (S i j) * ξ j + S i j * D i (ξ j) := by
    simp only [Derivation.leibniz, smul_eq_mul]
    simp only [mul_comm, add_comm]
  simp only [divergence, stressCurrent, map_sum, hp, Finset.sum_add_distrib,
    stressDivergence, Finset.sum_mul, contraction, covectorDerivative]
  rw [Finset.sum_comm (f := fun i j => D i (S i j) * ξ j)]

/-- Conformal Killing contraction, exposing the metric trace rather than Euclidean trace. -/
theorem conformalKilling_contraction (D : ι → Derivation ℝ A A)
    (S g : Matrix ι ι A) (ξ : ι → A) (σ : A)
    (hS : ∀ i j, S i j = S j i) (hξ : IsConformalKilling D g ξ σ) :
    contraction S (covectorDerivative D ξ) = σ * contraction S g := by
  change ∀ i j, D i (ξ j) + D j (ξ i) = 2 * σ * g i j at hξ
  rw [contraction_eq_half_symm S (covectorDerivative D ξ) hS]
  have hsum : contraction S (covectorDerivative D ξ + (covectorDerivative D ξ).transpose) =
      σ * contraction S g + σ * contraction S g := by
    unfold contraction
    simp only [Matrix.add_apply, Matrix.transpose_apply, covectorDerivative, hξ]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [two_mul, add_mul, mul_add]
    ac_rfl
  rw [hsum, smul_add, ← add_smul]
  norm_num

/-- Bessel--Hagen's stress-current identity including both off-shell source terms. -/
theorem divergence_stressCurrent_eq (D : ι → Derivation ℝ A A)
    (S g : Matrix ι ι A) (ξ : ι → A) (σ : A)
    (hS : ∀ i j, S i j = S j i) (hξ : IsConformalKilling D g ξ σ) :
    divergence D (stressCurrent S ξ) =
      (∑ j, stressDivergence D S j * ξ j) + σ * contraction S g := by
  rw [divergence_stressCurrent, conformalKilling_contraction D S g ξ σ hS hξ]

/-- For conserved stress, the metric trace is the exact conformal-current source. -/
theorem divergence_stressCurrent_eq_trace (D : ι → Derivation ℝ A A)
    (S g : Matrix ι ι A) (ξ : ι → A) (σ : A)
    (hS : ∀ i j, S i j = S j i) (hξ : IsConformalKilling D g ξ σ)
    (hdiv : ∀ j, stressDivergence D S j = 0) :
    divergence D (stressCurrent S ξ) = σ * contraction S g := by
  rw [divergence_stressCurrent_eq D S g ξ σ hS hξ]
  simp [hdiv]

/-- A symmetric, conserved, metric-traceless stress tensor gives conserved conformal currents. -/
theorem stressCurrent_conserved (D : ι → Derivation ℝ A A)
    (S g : Matrix ι ι A) (ξ : ι → A) (σ : A)
    (hS : ∀ i j, S i j = S j i) (hξ : IsConformalKilling D g ξ σ)
    (hdiv : ∀ j, stressDivergence D S j = 0) (htrace : contraction S g = 0) :
    divergence D (stressCurrent S ξ) = 0 := by
  rw [divergence_stressCurrent_eq_trace D S g ξ σ hS hξ hdiv, htrace, mul_zero]

/-- The gauge compensator `p = A·X` turns the potential variation into `Fᵢⱼ Xʲ`. -/
theorem gauge_compensated_characteristic (D : ι → Derivation ℝ A A)
    (potential X : ι → A) (i : ι) :
    -(∑ j, potential j * D i (X j)) + D i (∑ j, potential j * X j) -
        (∑ j, X j * D j (potential i)) =
      ∑ j, (D i (potential j) - D j (potential i)) * X j := by
  simp only [map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib]
  have hcomm : (∑ j, X j * D j (potential i)) = ∑ j, D j (potential i) * X j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcross : (∑ j, X j * D i (potential j)) = ∑ j, D i (potential j) * X j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcomm, hcross]
  ring

end InfoGeometry.Conformal.BesselHagenCurrent

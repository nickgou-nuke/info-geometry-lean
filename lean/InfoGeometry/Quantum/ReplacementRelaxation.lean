/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ReplacementStateChannel
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Relaxation toward an existing replacement state

On the full algebra of complex `n × n` matrices, the existing replacement
map `Rσ(X) = trace(X) • σ` is a projection when `trace σ = 1`. Its affine
combination with the identity gives complex-linear maps
`Φ(weight) = weight • id + (1 - weight) • Rσ`, with `Φ(weight).comp Φ(other) = Φ(weight * other)`.

Complex parameters express the algebraic identities without a scalar
restriction. Real parameters in `[0, 1]` give positive maps and preserve
positivity at every finite matrix amplification, using the existing
replacement-channel theorem. Trace preservation additionally uses
`trace σ = 1`.

The exponential parameter gives a differentiable relaxation path and its
linear generator, using Mathlib's native matrix L² operator norm. The centered
action and common-target two-stroke obstruction remain exact matrix identities.
These results do not construct
entropy, a thermodynamic Carnot cycle, or an energy-conserving metriplectic
bracket.
-/

noncomputable section

namespace InfoGeometry.Quantum.ReplacementRelaxation

open Matrix ReplacementStateChannel KrausAmplification
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- A normalized replacement map is an idempotent complex-linear operator. -/
theorem replacement_comp_self (σ : Mat) (hσ : Matrix.trace σ = 1) :
    (replacement σ).comp (replacement σ) = replacement σ := by
  apply LinearMap.ext
  intro X
  change Matrix.trace (replacement σ X) • σ = Matrix.trace X • σ
  rw [replacement_trace σ X hσ]

/-- Interpolate the identity and the existing replacement map. -/
def relaxation (σ : Mat) (weight : ℂ) : Mat →ₗ[ℂ] Mat :=
  weight • (LinearMap.id : Mat →ₗ[ℂ] Mat) + (1 - weight) • replacement σ

@[simp]
theorem relaxation_apply (σ : Mat) (weight : ℂ) (X : Mat) :
    relaxation σ weight X = weight • X + (1 - weight) • replacement σ X := rfl

@[simp]
theorem relaxation_zero (σ : Mat) : relaxation σ 0 = replacement σ := by
  simp [relaxation]

@[simp]
theorem relaxation_one (σ : Mat) :
    relaxation σ 1 = (LinearMap.id : Mat →ₗ[ℂ] Mat) := by
  simp [relaxation]

theorem relaxation_real_apply (σ : Mat) (weight : ℝ) (X : Mat) :
    relaxation σ (weight : ℂ) X = weight • X + (1 - weight) • replacement σ X := by
  ext i j
  change Complex.ofReal weight * X i j +
    (1 - Complex.ofReal weight) * (replacement σ X) i j =
    weight • X i j + (1 - weight) • (replacement σ X) i j
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]

/-- Real scalar multiplication retains the complex-linear operator carrier. -/
theorem relaxation_real_eq (σ : Mat) (weight : ℝ) :
    relaxation σ (weight : ℂ) =
      weight • (LinearMap.id : Mat →ₗ[ℂ] Mat) + (1 - weight) • replacement σ := by
  apply LinearMap.ext
  intro X
  change relaxation σ (weight : ℂ) X = weight • X + (1 - weight) • replacement σ X
  exact relaxation_real_apply σ weight X

/-- Normalizing the target makes every algebraic parameter trace preserving. -/
theorem relaxation_trace (σ : Mat) (hσ : Matrix.trace σ = 1)
    (weight : ℂ) (X : Mat) :
    Matrix.trace (relaxation σ weight X) = Matrix.trace X := by
  rw [relaxation_apply, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    replacement_trace σ X hσ]
  change weight * Matrix.trace X + (1 - weight) * Matrix.trace X = Matrix.trace X
  ring

/-- The normalized target is stationary for every algebraic parameter. -/
theorem relaxation_stationary (σ : Mat) (hσ : Matrix.trace σ = 1) (weight : ℂ) :
    relaxation σ weight σ = σ := by
  rw [relaxation_apply, replacement_on_density σ σ hσ, ← add_smul]
  simp

theorem replacement_relaxation (σ : Mat) (hσ : Matrix.trace σ = 1)
    (weight : ℂ) (X : Mat) :
    replacement σ (relaxation σ weight X) = replacement σ X := by
  change Matrix.trace (relaxation σ weight X) • σ = Matrix.trace X • σ
  rw [relaxation_trace σ hσ weight X]

/-- Composition multiplies the two parameters on the same full matrix carrier. -/
theorem relaxation_comp (σ : Mat) (hσ : Matrix.trace σ = 1) (weight other : ℂ) :
    (relaxation σ weight).comp (relaxation σ other) = relaxation σ (weight * other) := by
  apply LinearMap.ext
  intro X
  change weight • relaxation σ other X +
      (1 - weight) • replacement σ (relaxation σ other X) =
    (weight * other) • X + (1 - weight * other) • replacement σ X
  rw [replacement_relaxation σ hσ other X, relaxation_apply]
  simp only [smul_add, smul_smul]
  rw [add_assoc, ← add_smul,
    show weight * (1 - other) + (1 - weight) = 1 - weight * other by ring]

/-- Every traceless matrix is scaled, without a diagonal or commutation assumption. -/
theorem relaxation_of_trace_zero (σ : Mat) (weight : ℂ) (X : Mat)
    (hX : Matrix.trace X = 0) :
    relaxation σ weight X = weight • X := by
  simp [relaxation_apply, replacement, hX]

/-- The complementary part of a normalized replacement projection is traceless. -/
theorem trace_sub_replacement (σ : Mat) (hσ : Matrix.trace σ = 1) (X : Mat) :
    Matrix.trace (X - replacement σ X) = 0 := by
  rw [Matrix.trace_sub, replacement_trace σ X hσ, sub_self]

/-- The centered action is an exact identity for arbitrary matrix inputs. -/
theorem relaxation_sub_replacement (σ : Mat) (weight : ℂ) (X : Mat) :
    relaxation σ weight X - replacement σ X = weight • (X - replacement σ X) := by
  rw [relaxation_apply, sub_smul, one_smul, smul_sub]
  abel

/-- On trace-one inputs, the center is the target state itself. -/
theorem relaxation_sub_state (σ : Mat) (weight : ℂ) (X : Mat)
    (hX : Matrix.trace X = 1) :
    relaxation σ weight X - σ = weight • (X - σ) := by
  simpa only [replacement_on_density σ X hX] using
    relaxation_sub_replacement σ weight X

/-- For a nonidentity parameter, fixed matrices satisfy the replacement equation. -/
theorem relaxation_eq_self_iff (σ : Mat) (weight : ℂ) (hweight : weight ≠ 1) (X : Mat) :
    relaxation σ weight X = X ↔ X = replacement σ X := by
  constructor
  · intro h
    have hcenter := relaxation_sub_replacement σ weight X
    rw [h] at hcenter
    have hzero : (weight - 1) • (X - replacement σ X) = 0 := by
      rw [sub_smul, one_smul, ← hcenter, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hweight))
  · intro h
    rw [relaxation_apply, ← h, ← add_smul]
    simp

/-- Two strokes with a common normalized target cannot return a matrix outside
the replacement range unless their parameters multiply to one. -/
theorem two_stroke_return_eq_replacement (σ : Mat) (hσ : Matrix.trace σ = 1)
    (weight other : ℂ) (hweightother : weight * other ≠ 1) (X : Mat)
    (hreturn : relaxation σ weight (relaxation σ other X) = X) :
    X = replacement σ X := by
  apply (relaxation_eq_self_iff σ (weight * other) hweightother X).mp
  calc
    relaxation σ (weight * other) X = relaxation σ weight (relaxation σ other X) :=
      (LinearMap.congr_fun (relaxation_comp σ hσ weight other) X).symm
    _ = X := hreturn

/-- On trace-one matrices, a common-target two-stroke return is already equilibrium. -/
theorem two_stroke_return_eq_state (σ : Mat) (hσ : Matrix.trace σ = 1)
    (weight other : ℂ) (hweightother : weight * other ≠ 1) (X : Mat) (hX : Matrix.trace X = 1)
    (hreturn : relaxation σ weight (relaxation σ other X) = X) :
    X = σ := by
  exact (two_stroke_return_eq_replacement σ hσ weight other hweightother X hreturn).trans
    (replacement_on_density σ X hX)

/-- The same affine combination acts on every finite ancillary block. -/
theorem amplification_relaxation {r : Type*} [Fintype r] [DecidableEq r]
    (σ : Mat) (weight : ℂ) (X : Matrix (r × Fin n) (r × Fin n) ℂ) :
    amplification (r := r) (relaxation σ weight) X =
      weight • X + (1 - weight) • amplification (r := r) (replacement σ) X := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

/-- A real convex mixture preserves the native positive-semidefinite cone. -/
theorem relaxation_posSemidef (σ : Mat) (hσ : σ.PosSemidef)
    (weight : ℝ) (hweight : 0 ≤ weight) (hweight1 : weight ≤ 1) (X : Mat) (hX : X.PosSemidef) :
    (relaxation σ (weight : ℂ) X).PosSemidef := by
  rw [relaxation_real_apply]
  have hrep : (replacement σ X).PosSemidef := hσ.smul hX.trace_nonneg
  exact (hX.smul hweight).add (hrep.smul (sub_nonneg.mpr hweight1))

/-- Complete positivity follows for every finite ancillary index type from
the existing replacement-channel theorem and positive scalar combinations. -/
theorem relaxation_completely_positive {r : Type*} [Fintype r] [DecidableEq r]
    (σ : Mat) (hσ : σ.PosSemidef) (weight : ℝ) (hweight : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (X : Matrix (r × Fin n) (r × Fin n) ℂ) (hX : X.PosSemidef) :
    (amplification (r := r) (relaxation σ (weight : ℂ)) X).PosSemidef := by
  rw [amplification_relaxation]
  have hweight' : (0 : ℂ) ≤ (weight : ℂ) := Complex.zero_le_real.mpr hweight
  have hweight1' : (0 : ℂ) ≤ 1 - (weight : ℂ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      Complex.zero_le_real.mpr (sub_nonneg.mpr hweight1)
  exact (hX.smul hweight').add
    ((replacement_completely_positive_all σ hσ X hX).smul hweight1')

/-- The exponential parameter turns multiplication into additive time composition. -/
theorem relaxation_exp_add (σ : Mat) (hσ : Matrix.trace σ = 1) (γ s t : ℝ) :
    relaxation σ (Real.exp (-γ * (s + t)) : ℂ) =
      (relaxation σ (Real.exp (-γ * s) : ℂ)).comp
        (relaxation σ (Real.exp (-γ * t) : ℂ)) := by
  rw [relaxation_comp σ hσ]
  rw [mul_add, Real.exp_add, Complex.ofReal_mul]

/-- Nonnegative rate and time keep every finite amplification positive. -/
theorem relaxation_exp_completely_positive {r : Type*} [Fintype r] [DecidableEq r]
    (σ : Mat) (hσ : σ.PosSemidef) (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (X : Matrix (r × Fin n) (r × Fin n) ℂ) (hX : X.PosSemidef) :
    (amplification (r := r) (relaxation σ (Real.exp (-γ * t) : ℂ)) X).PosSemidef := by
  exact relaxation_completely_positive σ hσ (Real.exp (-γ * t))
    (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) ht)) X hX

/-- The explicit exponential matrix path satisfies its affine relaxation equation. -/
theorem hasDerivAt_relaxation_exp (σ : Mat) (γ t : ℝ) (X : Mat) :
    HasDerivAt (fun s : ℝ => relaxation σ (Real.exp (-γ * s) : ℂ) X)
      (γ • (replacement σ X - relaxation σ (Real.exp (-γ * t) : ℂ) X)) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-γ * s))
      (Real.exp (-γ * t) * (-γ)) t :=
    (hasDerivAt_const_mul (-γ)).exp
  have h := (he.smul_const X).add ((he.const_sub 1).smul_const (replacement σ X))
  convert h using 1
  · funext s
    exact relaxation_real_apply σ (Real.exp (-γ * s)) X
  · rw [relaxation_real_apply]
    module

/-- For a normalized target the derivative is the linear generator
`γ • (Rσ - id)` applied to the current matrix, on the same complex-linear carrier. -/
theorem hasDerivAt_relaxation_exp_generator (σ : Mat) (hσ : Matrix.trace σ = 1)
    (γ t : ℝ) (X : Mat) :
    HasDerivAt (fun s : ℝ => relaxation σ (Real.exp (-γ * s) : ℂ) X)
      ((γ • (replacement σ - (LinearMap.id : Mat →ₗ[ℂ] Mat)))
        (relaxation σ (Real.exp (-γ * t) : ℂ) X)) t := by
  simpa only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    replacement_relaxation σ hσ] using hasDerivAt_relaxation_exp σ γ t X

end InfoGeometry.Quantum.ReplacementRelaxation

end

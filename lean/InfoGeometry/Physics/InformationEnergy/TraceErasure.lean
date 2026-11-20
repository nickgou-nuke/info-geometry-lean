/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Holographic.BoundaryReconstruction
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis

/-!
# Trace erasure on the full matrix algebra

The native linear map `(Matrix.traceLinearMap n K K).smulRight sigma`
acts by `X ↦ trace X • sigma`. With `trace sigma = 1`, it is precisely the
encoding/decoding projector for trace and scalar state preparation. The
matrix `sigma` need not itself be idempotent. Arbitrary input matrices retain
their noncommutative multiplication throughout the defect calculation.

This is the algebraic formula of `Quantum.ReplacementStateChannel.replacement`,
stated directly using native Mathlib linear maps over any field. Positivity
and complete positivity remain in that existing owner; they are not inferred
from trace normalization here. Neither a heat cost nor particle annihilation
is derived from this finite algebraic erasure map.
-/

noncomputable section

namespace InfoGeometry.Physics.InformationEnergy.TraceErasure

open Matrix InfoGeometry.Holographic.BoundaryReconstruction

variable {K n : Type*} [Field K] [Fintype n]

local notation "Mat" => Matrix n n K
local notation "E" => Matrix.traceLinearMap n K K

/-- Trace encoding is a left inverse of normalized scalar state preparation. -/
theorem trace_preparation_split (σ : Mat) (hσ : Matrix.trace σ = 1) :
    (E).comp (LinearMap.toSpanSingleton K Mat σ) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp [LinearMap.toSpanSingleton, Matrix.traceLinearMap, hσ]

/-- The native trace reset is an idempotent superoperator, even for mixed output states. -/
theorem trace_reset_idempotent (σ : Mat) (hσ : Matrix.trace σ = 1) :
    ((E).smulRight σ).comp ((E).smulRight σ) = (E).smulRight σ := by
  change ((LinearMap.toSpanSingleton K Mat σ).comp E).comp
      ((LinearMap.toSpanSingleton K Mat σ).comp E) =
    (LinearMap.toSpanSingleton K Mat σ).comp E
  exact reconstruction_idempotent E _ (trace_preparation_split σ hσ)

/-- Two matrices survive the reset as the same output exactly when their traces agree. -/
theorem trace_reset_fiber_iff (σ X Y : Mat) (hσ : Matrix.trace σ = 1) :
    (E).smulRight σ X = (E).smulRight σ Y ↔ Matrix.trace X = Matrix.trace Y := by
  constructor
  · intro h
    have ht := congrArg Matrix.trace h
    simpa [Matrix.traceLinearMap, hσ] using ht
  · intro h
    change Matrix.trace X • σ = Matrix.trace Y • σ
    rw [h]

/-- The exact hidden operator space is the traceless subspace. -/
theorem trace_reset_kernel (σ : Mat) (hσ : Matrix.trace σ = 1) :
    LinearMap.ker ((E).smulRight σ) = LinearMap.ker E := by
  change LinearMap.ker ((LinearMap.toSpanSingleton K Mat σ).comp E) = LinearMap.ker E
  exact ker_reconstruction E _ (trace_preparation_split σ hσ)

/-- Only the line through the prepared matrix remains in the image. -/
theorem trace_reset_range (σ : Mat) (hσ : Matrix.trace σ = 1) :
    LinearMap.range ((E).smulRight σ) = Submodule.span K {σ} := by
  change LinearMap.range ((LinearMap.toSpanSingleton K Mat σ).comp E) = _
  rw [range_reconstruction E _ (trace_preparation_split σ hσ),
    LinearMap.range_toSpanSingleton]

/-- The existing reconstruction equivalence specializes to trace plus traceless remainder. -/
def traceSplitEquiv (σ : Mat) (hσ : Matrix.trace σ = 1) :
    Mat ≃ₗ[K] K × LinearMap.ker E :=
  splitEquiv E (LinearMap.toSpanSingleton K Mat σ) (trace_preparation_split σ hσ)

/-- Every commutator is hidden by trace erasure; the original products remain ordered. -/
theorem trace_reset_commutator (σ X Y : Mat) :
    (E).smulRight σ (X * Y - Y * X) = 0 := by
  simp [Matrix.traceLinearMap, Matrix.trace_mul_comm X Y]

/-- Exact failure of multiplicativity; no assumption `sigma * sigma = sigma` is made. -/
theorem trace_reset_product_defect (σ X Y : Mat) :
    (E).smulRight σ (X * Y) - (E).smulRight σ X * (E).smulRight σ Y =
      Matrix.trace (X * Y) • σ -
        (Matrix.trace X * Matrix.trace Y) • (σ * σ) := by
  change Matrix.trace (X * Y) • σ -
      (Matrix.trace X • σ) * (Matrix.trace Y • σ) = _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

variable [DecidableEq n]

/-- An off-diagonal matrix unit is nonzero but has zero reset output. -/
theorem trace_reset_not_injective (σ : Mat) {i j : n} (hij : i ≠ j) :
    ¬ Function.Injective ((E).smulRight σ) := by
  intro hinj
  have heq : (E).smulRight σ (Matrix.single i j 1) = (E).smulRight σ 0 := by
    simp [Matrix.traceLinearMap, Matrix.trace_single_eq_of_ne i j (1 : K) hij]
  have hz := hinj heq
  have hentry := congrArg (fun X : Mat => X i j) hz
  simp at hentry

/-- Resetting does not preserve multiplication on a matrix algebra with two indices. -/
theorem trace_reset_not_multiplicative (σ : Mat) (hσ : Matrix.trace σ = 1)
    {i j : n} (hij : i ≠ j) :
    ¬ (∀ X Y : Mat, (E).smulRight σ (X * Y) = (E).smulRight σ X * (E).smulRight σ Y) := by
  intro hmul
  have h := hmul (Matrix.single i j 1) (Matrix.single j i 1)
  have hσzero : σ = 0 := by
    simpa [Matrix.single_mul_single_same, Matrix.traceLinearMap,
      Matrix.trace_single_eq_of_ne i j (1 : K) hij, Matrix.trace_single_eq_of_ne j i (1 : K) hij.symm] using h
  simp [hσzero] at hσ

/-- No invertible conjugation on the same matrix algebra can implement trace erasure. -/
theorem trace_reset_not_conjugation (σ : Mat) {i j : n} (hij : i ≠ j)
    (U : Matˣ) :
    ¬ (∀ X : Mat, (E).smulRight σ X = (U : Mat) * X * (↑(U⁻¹) : Mat)) := by
  intro h
  apply trace_reset_not_injective σ hij
  intro X Y hXY
  have hconj : (U : Mat) * X * (↑(U⁻¹) : Mat) =
      (U : Mat) * Y * (↑(U⁻¹) : Mat) := (h X).symm.trans (hXY.trans (h Y))
  have hcancel := congrArg (fun Z : Mat => (↑(U⁻¹) : Mat) * Z * (U : Mat)) hconj
  simpa [mul_assoc] using hcancel

end InfoGeometry.Physics.InformationEnergy.TraceErasure

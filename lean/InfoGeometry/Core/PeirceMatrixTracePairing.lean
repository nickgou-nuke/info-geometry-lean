/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceDecomposition
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Opposite Peirce corners separate each other under the matrix trace pairing.
This proves algebraic nondegeneracy on supported matrices, over any commutative
ring. It does not identify a geometric cotangent bundle or assert a manifold.
-/
namespace InfoGeometry.Core.PeirceDecomposition
open Matrix
section CyclicFunctional
variable {A G : Type*} [Ring A] [AddCommGroup G]

/-- Under any cyclic additive functional `τ : A →+ G` on an associative ring `A`,
left pairing with `component10 P X` equals right pairing with `component01 P Y`. -/
theorem cyclic_component10_mul (τ : A →+ G)
    (hτ : ∀ U V : A, τ (U * V) = τ (V * U)) (P X Y : A) :
    τ (component10 P X * Y) = τ (X * component01 P Y) := by
  unfold component10 component01
  calc
    _ = τ (P * (X * complementIdempotent P * Y)) := by simp only [mul_assoc]
    _ = τ ((X * complementIdempotent P * Y) * P) := hτ _ _
    _ = _ := by simp only [mul_assoc]

/-- Under any cyclic additive functional `τ : A →+ G` on an associative ring `A`,
left pairing with `component01 P X` equals right pairing with `component10 P Y`. -/
theorem cyclic_component01_mul (τ : A →+ G)
    (hτ : ∀ U V : A, τ (U * V) = τ (V * U)) (P X Y : A) :
    τ (component01 P X * Y) = τ (X * component10 P Y) := by
  unfold component10 component01
  calc
    _ = τ (complementIdempotent P * (X * P * Y)) := by simp only [mul_assoc]
    _ = τ ((X * P * Y) * complementIdempotent P) := hτ _ _
    _ = _ := by simp only [mul_assoc]

end CyclicFunctional

section NoncommMatrixTrace
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

/-- Over any (possibly noncommutative) ring `R`, the matrix trace defect between
`component10 P X * Y` and `X * component01 P Y` equals the trace commutator of `P`
with `X * complementIdempotent P * Y`. -/
theorem trace_component10_mul_noncomm_anomaly (P X Y : Matrix n n R) :
    trace (component10 P X * Y) - trace (X * component01 P Y) =
      trace (P * (X * complementIdempotent P * Y) -
        (X * complementIdempotent P * Y) * P) := by
  unfold component10 component01
  rw [trace_sub]
  simp only [mul_assoc]

/-- Over any (possibly noncommutative) ring `R`, the matrix trace defect between
`component01 P X * Y` and `X * component10 P Y` equals the trace commutator of
`complementIdempotent P` with `X * P * Y`. -/
theorem trace_component01_mul_noncomm_anomaly (P X Y : Matrix n n R) :
    trace (component01 P X * Y) - trace (X * component10 P Y) =
      trace (complementIdempotent P * (X * P * Y) -
        (X * P * Y) * complementIdempotent P) := by
  unfold component10 component01
  rw [trace_sub]
  simp only [mul_assoc]

end NoncommMatrixTrace

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem trace_component10_mul (P X Y : Matrix n n R) :
    trace (component10 P X * Y) = trace (X * component01 P Y) := by
  unfold component10 component01
  calc
    _ = trace (P * (X * complementIdempotent P * Y)) := by simp only [mul_assoc]
    _ = trace ((X * complementIdempotent P * Y) * P) := trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

theorem trace_component01_mul (P X Y : Matrix n n R) :
    trace (component01 P X * Y) = trace (X * component10 P Y) := by
  unfold component10 component01
  calc
    _ = trace (complementIdempotent P * (X * P * Y)) := by simp only [mul_assoc]
    _ = trace ((X * P * Y) * complementIdempotent P) := trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

/-- Vanishing against every opposite corner forces a supported matrix to vanish. -/
theorem component10_eq_zero_of_trace_pairing (P X : Matrix n n R)
    (hX : component10 P X = X)
    (h : ∀ Y, trace (X * component01 P Y) = 0) : X = 0 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  rw [zero_mul, trace_zero, ← hX, trace_component10_mul]
  exact h Y

theorem component01_eq_zero_of_trace_pairing (P X : Matrix n n R)
    (hX : component01 P X = X)
    (h : ∀ Y, trace (X * component10 P Y) = 0) : X = 0 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  rw [zero_mul, trace_zero, ← hX, trace_component01_mul]
  exact h Y

end InfoGeometry.Core.PeirceDecomposition

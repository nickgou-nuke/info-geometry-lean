/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveMatrixCorner
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The actual full matrix representation has a canonical trace scale,
determined by the trace of either diagonal support. No positivity is used. -/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (τ : A →ₗ[R] R) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))
variable {d B : A}
include hτ

theorem trace_reflexive_square_zero (hd : d * d = 0) (hr : d * B * d = d) :
    τ d = 0 := by
  calc
    τ d = τ ((d * B) * d) := congrArg τ hr.symm
    _ = τ (d * (d * B)) := hτ _ _
    _ = 0 := by rw [← mul_assoc, hd, zero_mul, map_zero]

theorem trace_pairMatrixLinear
    (hd : d * d = 0) (hB : B * B = 0)
    (hr : d * B * d = d) (hs : B * d * B = B)
    (M : Matrix (Fin 2) (Fin 2) R) :
    τ (pairMatrixLinear d B M) = τ (d * B) * Matrix.trace M := by
  have htd := trace_reflexive_square_zero τ hτ hd hr
  have htB := trace_reflexive_square_zero τ hτ hB hs
  have htBd : τ (B * d) = τ (d * B) := hτ _ _
  simp [pairMatrixLinear_apply, pairMatrixUnit, htd, htB, htBd,
    Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  ring

theorem trace_pairMatrixLinear_mul
    (hd : d * d = 0) (hB : B * B = 0)
    (hr : d * B * d = d) (hs : B * d * B = B)
    (M N : Matrix (Fin 2) (Fin 2) R) :
    τ (pairMatrixLinear d B M * pairMatrixLinear d B N) =
      τ (d * B) * Matrix.trace (M * N) := by
  rw [← pairMatrixLinear_mul hd hB hr hs]
  exact trace_pairMatrixLinear τ hτ hd hB hr hs _

theorem trace_pair_support_scale (hfull : support d B = 1) :
    2 * τ (d * B) = τ (1 : A) := by
  calc
    2 * τ (d * B) = τ (d * B) + τ (B * d) := by rw [hτ B d]; ring
    _ = τ (support d B) := by rw [support, map_add]
    _ = τ (1 : A) := congrArg τ hfull

end InfoGeometry.Canonical.ReflexiveNilpotentFlows

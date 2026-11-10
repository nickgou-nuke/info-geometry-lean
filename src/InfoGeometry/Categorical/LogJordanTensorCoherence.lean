/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LogJordanTensorFusion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# InfoGeometry.Categorical.LogJordanTensorCoherence

Nearest coherence layer for the logarithmic Jordan tensor sector.

`Canonical.LogJordanTensorFusion` proves that the primitive logarithmic
nilpotent on two rank-two Jordan sectors is

`N₁₂ = N ⊗ id + id ⊗ N`.

This file proves that the canonical module tensor associator transports the
three-factor logarithmic nilpotent between the two parenthesizations, and that
the canonical tensor swap intertwines the two-factor logarithmic nilpotent.
These are the local naturality statements required before the ambient tensor
pentagon and symmetric/braided hexagon can be restricted to the logarithmic
sector.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace InfoGeometry.Categorical.LogJordanTensorCoherence

open scoped TensorProduct

open InfoGeometry.Canonical.LogJordanTensorFusion

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem logJordanTensorCoherence_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

section NoncommRing

variable {B : Type*} [Ring B]

/-- In any noncommutative ring `[Ring B]`, an operator `T` that intertwines three
generators `N₁, N₂, N₃` intertwines their three-factor Leibniz sum `N₁ + N₂ + N₃`. -/
theorem ring_intertwine_triple_sum {T N₁ N₂ N₃ : B}
    (h1 : T * N₁ = N₁ * T) (h2 : T * N₂ = N₂ * T) (h3 : T * N₃ = N₃ * T) :
    T * (N₁ + N₂ + N₃) = (N₁ + N₂ + N₃) * T := by
  calc
    T * (N₁ + N₂ + N₃) = T * N₁ + T * N₂ + T * N₃ := by noncomm_ring
    _ = N₁ * T + N₂ * T + N₃ * T := by rw [h1, h2, h3]
    _ = (N₁ + N₂ + N₃) * T := by noncomm_ring

end NoncommRing

variable {𝕜 : Type*} [Field 𝕜]

abbrev J (𝕜 : Type*) [Field 𝕜] := JordanCarrier 𝕜

/-- Three-factor logarithmic nilpotent in the left-associated carrier
`(J ⊗ J) ⊗ J`. -/
def logTripleNilpotentLeft :
    Module.End 𝕜 ((J 𝕜 ⊗[𝕜] J 𝕜) ⊗[𝕜] J 𝕜) :=
  TensorProduct.map
      (logTensorNilpotentEnd (𝕜 := 𝕜))
      (LinearMap.id : Module.End 𝕜 (J 𝕜)) +
    TensorProduct.map
      (LinearMap.id : Module.End 𝕜 (J 𝕜 ⊗[𝕜] J 𝕜))
      (jordanNilpotentLinear (𝕜 := 𝕜))

/-- Three-factor logarithmic nilpotent in the right-associated carrier
`J ⊗ (J ⊗ J)`. -/
def logTripleNilpotentRight :
    Module.End 𝕜 (J 𝕜 ⊗[𝕜] (J 𝕜 ⊗[𝕜] J 𝕜)) :=
  TensorProduct.map
      (jordanNilpotentLinear (𝕜 := 𝕜))
      (LinearMap.id : Module.End 𝕜 (J 𝕜 ⊗[𝕜] J 𝕜)) +
    TensorProduct.map
      (LinearMap.id : Module.End 𝕜 (J 𝕜))
      (logTensorNilpotentEnd (𝕜 := 𝕜))

/-- Pure-tensor action of the left-associated three-factor nilpotent. -/
@[simp]
theorem logTripleNilpotentLeft_apply_tmul
    (u v w : J 𝕜) :
    logTripleNilpotentLeft (𝕜 := 𝕜)
        ((u ⊗ₜ[𝕜] v) ⊗ₜ[𝕜] w) =
      (jordanNilpotentLinear (𝕜 := 𝕜) u ⊗ₜ[𝕜] v) ⊗ₜ[𝕜] w +
      (u ⊗ₜ[𝕜] jordanNilpotentLinear (𝕜 := 𝕜) v) ⊗ₜ[𝕜] w +
      (u ⊗ₜ[𝕜] v) ⊗ₜ[𝕜] jordanNilpotentLinear (𝕜 := 𝕜) w := by
  simp [logTripleNilpotentLeft, TensorProduct.map_tmul,
    logTensorNilpotentEnd_apply_tmul, TensorProduct.add_tmul,
    TensorProduct.tmul_add, add_assoc]

/-- Pure-tensor action of the right-associated three-factor nilpotent. -/
@[simp]
theorem logTripleNilpotentRight_apply_tmul
    (u v w : J 𝕜) :
    logTripleNilpotentRight (𝕜 := 𝕜)
        (u ⊗ₜ[𝕜] (v ⊗ₜ[𝕜] w)) =
      jordanNilpotentLinear (𝕜 := 𝕜) u ⊗ₜ[𝕜] (v ⊗ₜ[𝕜] w) +
      u ⊗ₜ[𝕜]
        (jordanNilpotentLinear (𝕜 := 𝕜) v ⊗ₜ[𝕜] w) +
      u ⊗ₜ[𝕜]
        (v ⊗ₜ[𝕜] jordanNilpotentLinear (𝕜 := 𝕜) w) := by
  simp [logTripleNilpotentRight, TensorProduct.map_tmul,
    logTensorNilpotentEnd_apply_tmul, TensorProduct.add_tmul,
    TensorProduct.tmul_add, add_assoc]

/-- The canonical tensor associator is an intertwiner of the three-factor
logarithmic nilpotent. -/
theorem tensorAssoc_intertwines_logTripleNilpotent :
    (TensorProduct.assoc 𝕜 (J 𝕜) (J 𝕜) (J 𝕜)).toLinearMap.comp
        (logTripleNilpotentLeft (𝕜 := 𝕜)) =
      (logTripleNilpotentRight (𝕜 := 𝕜)).comp
        (TensorProduct.assoc 𝕜 (J 𝕜) (J 𝕜) (J 𝕜)).toLinearMap := by
  apply TensorProduct.ext_threefold
  intro u v w
  simp only [LinearMap.comp_apply, map_add, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul,
    logTripleNilpotentLeft_apply_tmul,
    logTripleNilpotentRight_apply_tmul, TensorProduct.add_tmul,
    TensorProduct.tmul_add]

/-- The canonical tensor swap is an intertwiner of the two-factor logarithmic
nilpotent. -/
theorem tensorComm_intertwines_logTensorNilpotent :
    (TensorProduct.comm 𝕜 (J 𝕜) (J 𝕜)).toLinearMap.comp
        (logTensorNilpotentEnd (𝕜 := 𝕜)) =
      (logTensorNilpotentEnd (𝕜 := 𝕜)).comp
        (TensorProduct.comm 𝕜 (J 𝕜) (J 𝕜)).toLinearMap := by
  ext u v
  simp [LinearMap.comp_apply, TensorProduct.comm_tmul,
    logTensorNilpotentEnd_apply_tmul, add_comm]

/-- Braiding covariance for the full logarithmic zero mode: swapping the two
factors also swaps their conformal weights. -/
theorem tensorComm_intertwines_logTensorZeroMode
    (Δ₁ Δ₂ : 𝕜) :
    (TensorProduct.comm 𝕜 (J 𝕜) (J 𝕜)).toLinearMap.comp
        (logTensorZeroMode Δ₁ Δ₂) =
      (logTensorZeroMode Δ₂ Δ₁).comp
        (TensorProduct.comm 𝕜 (J 𝕜) (J 𝕜)).toLinearMap := by
  ext u v
  simp [LinearMap.comp_apply, TensorProduct.comm_tmul,
    logTensorZeroMode_apply_tmul, logTensorNilpotentEnd_apply_tmul,
    add_assoc, add_comm, add_left_comm]

end InfoGeometry.Categorical.LogJordanTensorCoherence

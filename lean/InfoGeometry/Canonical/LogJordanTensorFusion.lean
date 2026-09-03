import InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
import InfoGeometry.Canonical.ModularCoproductFlux
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# InfoGeometry.Canonical.LogJordanTensorFusion

First categorical-algebraic bridge from the logarithmic Virasoro Jordan cell to
tensor-product fusion.

The owner theorem `ModularCoproductFlux.tensorJordanNilpotent_sq` proves that the
primitive tensor sum of two square-zero nilpotents

`N₁ ⊗ 1 + 1 ⊗ N₂`

has square `2 • (N₁ ⊗ N₂)` and cube zero.  This file instantiates that theorem
with the actual rank-two logarithmic Jordan nilpotent used by
`LogJordanVirasoroIntertwiner` and then lifts the result to an endomorphism of
the actual tensor-product carrier `(𝕜²) ⊗ (𝕜²)`.

It also proves the full zero-mode fusion law

`L₀(Δ₁) ⊗ id + id ⊗ L₀(Δ₂) = (Δ₁ + Δ₂) id + N₁₂`,

with `N₁₂³ = 0`.  Thus the tensor product is a generalized eigenspace of weight
`Δ₁ + Δ₂` with logarithmic depth at most three.

This is the nearest formal DAG edge toward a tensor-closed
non-semisimple/logarithmic monoidal sector; no braided-category packaging is
asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.LogJordanTensorFusion

open scoped TensorProduct

open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Canonical.ModularCoproductFlux

variable {𝕜 : Type*} [Field 𝕜]

/-! ## Tensor-algebra level -/

abbrev JordanEnd (𝕜 : Type*) [Field 𝕜] := Matrix (Fin 2) (Fin 2) 𝕜

abbrev JordanTensorEnd (𝕜 : Type*) [Field 𝕜] :=
  JordanEnd 𝕜 ⊗[𝕜] JordanEnd 𝕜

/-- The primitive nilpotent part on the tensor product of two logarithmic
rank-two Jordan sectors. -/
def logTensorNilpotent : JordanTensorEnd 𝕜 :=
  tensorJordanNilpotent (R := 𝕜)
    (jordanNilpotent 𝕜) (jordanNilpotent 𝕜)

/-- The logarithmic Jordan generator used in each factor is square-zero. -/
theorem jordanNilpotent_sq_zero :
    jordanNilpotent 𝕜 * jordanNilpotent 𝕜 = 0 :=
  (zero_mode_subspace_indecomposable (𝕜 := 𝕜)).2

/-- Tensor fusion raises the possible Jordan depth: the square of the primitive
nilpotent is exactly the mixed tensor term. -/
theorem logTensorNilpotent_sq :
    logTensorNilpotent (𝕜 := 𝕜) * logTensorNilpotent (𝕜 := 𝕜) =
      (2 : 𝕜) •
        (jordanNilpotent 𝕜 ⊗ₜ[𝕜] jordanNilpotent 𝕜 : JordanTensorEnd 𝕜) := by
  simpa [logTensorNilpotent] using
    (tensorJordanNilpotent_sq (R := 𝕜)
      (jordanNilpotent 𝕜) (jordanNilpotent 𝕜)
      (jordanNilpotent_sq_zero (𝕜 := 𝕜))
      (jordanNilpotent_sq_zero (𝕜 := 𝕜)))

/-- The primitive tensor nilpotent of two rank-two logarithmic Jordan sectors
is nilpotent of order at most three. -/
theorem logTensorNilpotent_cube_zero :
    logTensorNilpotent (𝕜 := 𝕜) * logTensorNilpotent (𝕜 := 𝕜) *
        logTensorNilpotent (𝕜 := 𝕜) = 0 := by
  simpa [logTensorNilpotent] using
    (tensorJordanNilpotent_cube_zero (R := 𝕜)
      (jordanNilpotent 𝕜) (jordanNilpotent 𝕜)
      (jordanNilpotent_sq_zero (𝕜 := 𝕜))
      (jordanNilpotent_sq_zero (𝕜 := 𝕜)))

/-- The tensor-fusion nilpotent is the sum of the two factor nilpotents acting
on their respective tensor legs. -/
theorem logTensorNilpotent_eq :
    logTensorNilpotent (𝕜 := 𝕜) =
      (jordanNilpotent 𝕜 ⊗ₜ[𝕜] (1 : JordanEnd 𝕜)) +
      ((1 : JordanEnd 𝕜) ⊗ₜ[𝕜] jordanNilpotent 𝕜) := by
  rfl

/-! ## Actual tensor-product module level -/

/-- Carrier of one rank-two logarithmic Jordan sector. -/
abbrev JordanCarrier (𝕜 : Type*) [Field 𝕜] := Fin 2 → 𝕜

/-- The Jordan nilpotent as an actual linear endomorphism of the rank-two
carrier. -/
def jordanNilpotentLinear : Module.End 𝕜 (JordanCarrier 𝕜) :=
  Matrix.toLin' (jordanNilpotent 𝕜)

/-- The linear Jordan nilpotent is square-zero on the carrier. -/
theorem jordanNilpotentLinear_sq_zero :
    (jordanNilpotentLinear (𝕜 := 𝕜)).comp
        (jordanNilpotentLinear (𝕜 := 𝕜)) = 0 := by
  ext v
  change jordanNilpotent 𝕜 *ᵥ (jordanNilpotent 𝕜 *ᵥ v) = 0
  rw [← Matrix.mulVec_mulVec]
  rw [jordanNilpotent_sq_zero]
  simp

/-- Pointwise square-zero law for the linear Jordan nilpotent. -/
@[simp]
theorem jordanNilpotentLinear_apply_twice (v : JordanCarrier 𝕜) :
    jordanNilpotentLinear (𝕜 := 𝕜)
        (jordanNilpotentLinear (𝕜 := 𝕜) v) = 0 := by
  have h := LinearMap.congr_fun (jordanNilpotentLinear_sq_zero (𝕜 := 𝕜)) v
  simpa [LinearMap.comp_apply] using h

/-- Primitive logarithmic nilpotent acting on the actual tensor-product module.
It is `N ⊗ id + id ⊗ N`. -/
def logTensorNilpotentEnd :
    Module.End 𝕜 (JordanCarrier 𝕜 ⊗[𝕜] JordanCarrier 𝕜) :=
  TensorProduct.map
      (jordanNilpotentLinear (𝕜 := 𝕜))
      (LinearMap.id : Module.End 𝕜 (JordanCarrier 𝕜)) +
    TensorProduct.map
      (LinearMap.id : Module.End 𝕜 (JordanCarrier 𝕜))
      (jordanNilpotentLinear (𝕜 := 𝕜))

/-- Pure-tensor action of the logarithmic tensor nilpotent. -/
@[simp]
theorem logTensorNilpotentEnd_apply_tmul
    (u v : JordanCarrier 𝕜) :
    logTensorNilpotentEnd (𝕜 := 𝕜) (u ⊗ₜ[𝕜] v) =
      jordanNilpotentLinear (𝕜 := 𝕜) u ⊗ₜ[𝕜] v +
      u ⊗ₜ[𝕜] jordanNilpotentLinear (𝕜 := 𝕜) v := by
  simp [logTensorNilpotentEnd, TensorProduct.map_tmul]

/-- On pure tensors, the square of the actual tensor-product nilpotent is the
mixed action `2 • (N u ⊗ N v)`. -/
@[simp]
theorem logTensorNilpotentEnd_sq_tmul
    (u v : JordanCarrier 𝕜) :
    ((logTensorNilpotentEnd (𝕜 := 𝕜)).comp
        (logTensorNilpotentEnd (𝕜 := 𝕜))) (u ⊗ₜ[𝕜] v) =
      (2 : 𝕜) •
        (jordanNilpotentLinear (𝕜 := 𝕜) u ⊗ₜ[𝕜]
          jordanNilpotentLinear (𝕜 := 𝕜) v) := by
  simp [LinearMap.comp_apply, logTensorNilpotentEnd_apply_tmul, two_smul,
    add_assoc, add_comm, add_left_comm]

/-- Global square law on the actual tensor-product module. -/
theorem logTensorNilpotentEnd_sq :
    (logTensorNilpotentEnd (𝕜 := 𝕜)).comp
        (logTensorNilpotentEnd (𝕜 := 𝕜)) =
      (2 : 𝕜) • TensorProduct.map
        (jordanNilpotentLinear (𝕜 := 𝕜))
        (jordanNilpotentLinear (𝕜 := 𝕜)) := by
  ext u v
  simpa [TensorProduct.map_tmul] using
    (logTensorNilpotentEnd_sq_tmul (𝕜 := 𝕜) u v)

/-- The actual tensor-product nilpotent is nilpotent of order at most three. -/
theorem logTensorNilpotentEnd_cube_zero :
    ((logTensorNilpotentEnd (𝕜 := 𝕜)).comp
        (logTensorNilpotentEnd (𝕜 := 𝕜))).comp
      (logTensorNilpotentEnd (𝕜 := 𝕜)) = 0 := by
  ext u v
  simp [LinearMap.comp_apply, logTensorNilpotentEnd_apply_tmul,
    logTensorNilpotentEnd_sq_tmul]

/-! ## Full zero-mode fusion law -/

/-- The full rank-two logarithmic Jordan cell as a linear endomorphism. -/
def jordanCellLinear (Δ : 𝕜) : Module.End 𝕜 (JordanCarrier 𝕜) :=
  Matrix.toLin' (jordanCell Δ)

/-- Every logarithmic Jordan cell is its scalar weight plus the universal
nilpotent shift. -/
@[simp]
theorem jordanCellLinear_apply (Δ : 𝕜) (v : JordanCarrier 𝕜) :
    jordanCellLinear Δ v =
      Δ • v + jordanNilpotentLinear (𝕜 := 𝕜) v := by
  ext i
  fin_cases i <;>
    simp [jordanCellLinear, jordanNilpotentLinear, jordanCell,
      jordanNilpotent, Matrix.mulVec, Fin.sum_univ_two]

/-- Coproduct/primitive zero-mode action on two logarithmic Jordan sectors. -/
def logTensorZeroMode (Δ₁ Δ₂ : 𝕜) :
    Module.End 𝕜 (JordanCarrier 𝕜 ⊗[𝕜] JordanCarrier 𝕜) :=
  TensorProduct.map
      (jordanCellLinear Δ₁)
      (LinearMap.id : Module.End 𝕜 (JordanCarrier 𝕜)) +
    TensorProduct.map
      (LinearMap.id : Module.End 𝕜 (JordanCarrier 𝕜))
      (jordanCellLinear Δ₂)

/-- On pure tensors, conformal weights add and the residual logarithmic part is
exactly `N ⊗ id + id ⊗ N`. -/
@[simp]
theorem logTensorZeroMode_apply_tmul
    (Δ₁ Δ₂ : 𝕜) (u v : JordanCarrier 𝕜) :
    logTensorZeroMode Δ₁ Δ₂ (u ⊗ₜ[𝕜] v) =
      (Δ₁ + Δ₂) • (u ⊗ₜ[𝕜] v) +
        logTensorNilpotentEnd (𝕜 := 𝕜) (u ⊗ₜ[𝕜] v) := by
  rw [logTensorNilpotentEnd_apply_tmul]
  simp [logTensorZeroMode, jordanCellLinear_apply, TensorProduct.map_tmul,
    TensorProduct.add_tmul, TensorProduct.tmul_add, add_smul]
  module

/-- Global tensor-fusion law for two logarithmic rank-two zero modes:
`L₀₁₂ = (Δ₁ + Δ₂) id + N₁₂`. -/
theorem logTensorZeroMode_eq_weight_add_nilpotent
    (Δ₁ Δ₂ : 𝕜) :
    logTensorZeroMode Δ₁ Δ₂ =
      (Δ₁ + Δ₂) •
          (LinearMap.id : Module.End 𝕜
            (JordanCarrier 𝕜 ⊗[𝕜] JordanCarrier 𝕜)) +
        logTensorNilpotentEnd (𝕜 := 𝕜) := by
  ext u v
  simpa using (logTensorZeroMode_apply_tmul (𝕜 := 𝕜) Δ₁ Δ₂ u v)

/-- Zero mode centered at the summed conformal weight. -/
def centeredLogTensorZeroMode (Δ₁ Δ₂ : 𝕜) :
    Module.End 𝕜 (JordanCarrier 𝕜 ⊗[𝕜] JordanCarrier 𝕜) :=
  logTensorZeroMode Δ₁ Δ₂ -
    (Δ₁ + Δ₂) •
      (LinearMap.id : Module.End 𝕜
        (JordanCarrier 𝕜 ⊗[𝕜] JordanCarrier 𝕜))

/-- Centering the fused zero mode removes exactly the scalar conformal weight
and leaves the logarithmic tensor nilpotent. -/
theorem centeredLogTensorZeroMode_eq_nilpotent
    (Δ₁ Δ₂ : 𝕜) :
    centeredLogTensorZeroMode Δ₁ Δ₂ =
      logTensorNilpotentEnd (𝕜 := 𝕜) := by
  rw [centeredLogTensorZeroMode, logTensorZeroMode_eq_weight_add_nilpotent]
  abel

/-- The tensor product of two rank-two logarithmic zero-mode sectors is a
generalized eigenspace of weight `Δ₁ + Δ₂` with nilpotent depth at most three. -/
theorem centeredLogTensorZeroMode_cube_zero
    (Δ₁ Δ₂ : 𝕜) :
    ((centeredLogTensorZeroMode Δ₁ Δ₂).comp
        (centeredLogTensorZeroMode Δ₁ Δ₂)).comp
      (centeredLogTensorZeroMode Δ₁ Δ₂) = 0 := by
  rw [centeredLogTensorZeroMode_eq_nilpotent]
  exact logTensorNilpotentEnd_cube_zero (𝕜 := 𝕜)

end InfoGeometry.Canonical.LogJordanTensorFusion

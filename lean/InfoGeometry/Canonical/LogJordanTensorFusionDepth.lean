import InfoGeometry.Canonical.LogJordanTensorFusion

/-!
# InfoGeometry.Canonical.LogJordanTensorFusionDepth

Closes the distinction between "nilpotent of order at most three" and a
genuine order-three logarithmic tensor Jordan direction.

For the standard rank-two Jordan nilpotent `N`, the tensor primitive sum

`N₁₂ = N ⊗ id + id ⊗ N`

already satisfies `N₁₂³ = 0`.  This file proves that in characteristic zero its
square is nonzero by evaluating it on the explicit top logarithmic state
`e₁ ⊗ e₁` and detecting the resulting `2 • (e₀ ⊗ e₀)` with a tensor-coordinate
functional.
-/

noncomputable section

namespace InfoGeometry.Canonical.LogJordanTensorFusionDepth

open scoped TensorProduct
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Canonical.LogJordanTensorFusion

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Coordinate functional selecting the primary coordinate `0`. -/
def coord0 : JordanCarrier 𝕜 →ₗ[𝕜] 𝕜 where
  toFun := fun v => v 0
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

/-- Tensor coordinate functional `(u ⊗ v) ↦ u₀ v₀`. -/
def coord00 :
    JordanCarrier 𝕜 ⊗[𝕜] JordanCarrier 𝕜 →ₗ[𝕜] 𝕜 :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun v => u 0 * v 0
          map_add' := by
            intro v w
            simp [mul_add]
          map_smul' := by
            intro c v
            simp [mul_assoc, mul_comm, mul_left_comm] }
      map_add' := by
        intro u v
        ext w
        simp [add_mul]
      map_smul' := by
        intro c u
        ext v
        simp [mul_assoc] }

@[simp]
theorem coord00_tmul (u v : JordanCarrier 𝕜) :
    coord00 (𝕜 := 𝕜) (u ⊗ₜ[𝕜] v) = u 0 * v 0 := by
  rfl

@[simp]
theorem coord00_e0_tmul_e0 :
    coord00 (𝕜 := 𝕜)
      ((e0 : JordanCarrier 𝕜) ⊗ₜ[𝕜] (e0 : JordanCarrier 𝕜)) = 1 := by
  simp [coord00_tmul, e0, Pi.single]

/-- The primary tensor state is nonzero. -/
theorem e0_tmul_e0_ne_zero :
    ((e0 : JordanCarrier 𝕜) ⊗ₜ[𝕜] (e0 : JordanCarrier 𝕜)) ≠ 0 := by
  intro h
  have hdet := congrArg (coord00 (𝕜 := 𝕜)) h
  have : (1 : 𝕜) = 0 := by
    simpa [coord00_tmul, e0, Pi.single] using hdet
  exact one_ne_zero this

/-- In characteristic zero the second Jordan-chain state
`2 • (e₀ ⊗ e₀)` is nonzero. -/
theorem two_smul_e0_tmul_e0_ne_zero :
    (2 : 𝕜) •
        ((e0 : JordanCarrier 𝕜) ⊗ₜ[𝕜] (e0 : JordanCarrier 𝕜)) ≠ 0 := by
  intro h
  have hdet := congrArg (coord00 (𝕜 := 𝕜)) h
  have htwo : (2 : 𝕜) = 0 := by
    simpa [coord00_tmul, e0, Pi.single] using hdet
  exact OfNat.ofNat_ne_zero 2 htwo

/-- The square of the tensor logarithmic nilpotent is genuinely nonzero.
Together with `logTensorNilpotentEnd_cube_zero`, this proves exact nilpotency
order three. -/
theorem logTensorNilpotentEnd_sq_ne_zero :
    (logTensorNilpotentEnd (𝕜 := 𝕜)).comp
        (logTensorNilpotentEnd (𝕜 := 𝕜)) ≠ 0 := by
  intro hzero
  have heval := LinearMap.congr_fun hzero
    ((e1 : JordanCarrier 𝕜) ⊗ₜ[𝕜] (e1 : JordanCarrier 𝕜))
  have hchain := logTensorNilpotentEnd_sq_e1_tmul_e1 (𝕜 := 𝕜)
  rw [hzero] at hchain
  simp only [LinearMap.zero_apply] at hchain
  exact two_smul_e0_tmul_e0_ne_zero (𝕜 := 𝕜) hchain.symm

/-- Exact rank-two tensor-fusion nilpotency statement:
`N₁₂² ≠ 0` and `N₁₂³ = 0`. -/
theorem logTensorNilpotentEnd_exact_order_three :
    (logTensorNilpotentEnd (𝕜 := 𝕜)).comp
          (logTensorNilpotentEnd (𝕜 := 𝕜)) ≠ 0 ∧
      ((logTensorNilpotentEnd (𝕜 := 𝕜)).comp
          (logTensorNilpotentEnd (𝕜 := 𝕜))).comp
        (logTensorNilpotentEnd (𝕜 := 𝕜)) = 0 := by
  exact ⟨logTensorNilpotentEnd_sq_ne_zero (𝕜 := 𝕜),
    logTensorNilpotentEnd_cube_zero (𝕜 := 𝕜)⟩

/-- The centered fused zero mode has genuine logarithmic depth three. -/
theorem centeredLogTensorZeroMode_exact_order_three
    (Δ₁ Δ₂ : 𝕜) :
    (centeredLogTensorZeroMode Δ₁ Δ₂).comp
          (centeredLogTensorZeroMode Δ₁ Δ₂) ≠ 0 ∧
      ((centeredLogTensorZeroMode Δ₁ Δ₂).comp
          (centeredLogTensorZeroMode Δ₁ Δ₂)).comp
        (centeredLogTensorZeroMode Δ₁ Δ₂) = 0 := by
  rw [centeredLogTensorZeroMode_eq_nilpotent]
  exact logTensorNilpotentEnd_exact_order_three (𝕜 := 𝕜)

end InfoGeometry.Canonical.LogJordanTensorFusionDepth

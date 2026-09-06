import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Basic

open Filter Topology

theorem einstein_bose_limit (A B : ℝ) (_hB : B ≠ 0) :
  Tendsto (fun ρ : ℝ => A / (B * ρ) + 1) atTop (𝓝 1) := by
  have h1 : Tendsto (fun ρ : ℝ => A / (B * ρ)) atTop (𝓝 0) := by
    have h2 : (fun ρ : ℝ => A / (B * ρ)) = (fun ρ : ℝ => (A / B) * ρ⁻¹) := by
      ext ρ
      calc A / (B * ρ) = A * (B * ρ)⁻¹ := rfl
        _ = A * (B⁻¹ * ρ⁻¹) := by rw [mul_inv]
        _ = (A * B⁻¹) * ρ⁻¹ := by rw [← mul_assoc]
        _ = (A / B) * ρ⁻¹ := rfl
    rw [h2]
    have h3 : Tendsto (fun ρ : ℝ => ρ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have h4 := Tendsto.const_mul (A / B) h3
    rw [mul_zero] at h4
    exact h4
  have h5 := Tendsto.add_const 1 h1
  rw [zero_add] at h5
  exact h5

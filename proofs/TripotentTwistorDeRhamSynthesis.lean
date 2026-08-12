import Mathlib
import proofs.SpinNetworkTwistorQuantization

noncomputable section

namespace TripotentTwistorDeRhamSynthesis

open Real Matrix

/-!
# Synthesis of Tripotent, Twistor, and de Rham Thermodynamics

This module reconciles the tripotent chiral cone, twistor quantization, and
de Rham entropy structures as described in the architecture plan.
-/

-- 1. Trifurcation from tripotent
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem tripotent_trifurcation_vectors (T : Module.End ℝ V) (hT : T ^ 3 = T) (v : V) :
    ∃ v1 v0 v_1 : V, v = v1 + v0 + v_1 ∧ T v1 = v1 ∧ T v0 = 0 ∧ T v_1 = -v_1 := by
  let v1 := (1/2:ℝ) • (T (T v) + T v)
  let v_1 := (1/2:ℝ) • (T (T v) - T v)
  let v0 := v - T (T v)
  use v1, v0, v_1
  have hT3 : ∀ x, T (T (T x)) = T x := LinearMap.ext_iff.mp hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [v1, v0, v_1]
    rw [smul_add, smul_sub]
    have h_assoc : (1/2:ℝ) • T (T v) + (1/2:ℝ) • T v + (v - T (T v)) + ((1/2:ℝ) • T (T v) - (1/2:ℝ) • T v) =
        ((1/2:ℝ) • T (T v) + (1/2:ℝ) • T (T v)) + ((1/2:ℝ) • T v - (1/2:ℝ) • T v) + v - T (T v) := by abel
    rw [h_assoc]
    have h1 : (1/2:ℝ) • T (T v) + (1/2:ℝ) • T (T v) = T (T v) := by rw [← add_smul]; norm_num
    have h2 : (1/2:ℝ) • T v - (1/2:ℝ) • T v = 0 := sub_self _
    rw [h1, h2]
    abel
  · dsimp [v1]; rw [map_smul, map_add, hT3]
    have h_comm : T v + T (T v) = T (T v) + T v := by rw [add_comm]
    rw [h_comm]
  · dsimp [v0]; rw [map_sub, hT3, sub_self]
  · dsimp [v_1]; rw [map_smul, map_sub, hT3]
    have h_neg : T v - T (T v) = -(T (T v) - T v) := by rw [← neg_sub]
    rw [h_neg, smul_neg]

-- 2. de Rham 1-form d(ln Q)
theorem d_lnQ_is_entropy_potential (x : ℝ) (hx : 0 < x) :
    deriv (fun y => y * Real.log y - y) x = Real.log x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_deriv_step : ∀ᶠ y in nhds x, deriv (fun z => z * Real.log z - z) y = Real.log y := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    have h_has := (hasDerivAt_mul_log hy).sub (hasDerivAt_id y)
    have h_eq : deriv (fun z => z * Real.log z - z) y = Real.log y + 1 - 1 := h_has.deriv
    rw [h_eq]
    ring
  exact h_deriv_step.self_of_nhds

-- 3. Fisher = Hessian of entropy
theorem fisher_is_hessian_entropy (x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun y => y * Real.log y - y)) x = 1 / x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have h_deriv_step : ∀ᶠ y in nhds x, deriv (fun z => z * Real.log z - z) y = Real.log y := by
    filter_upwards [eventually_ne_nhds hx'] with y hy
    have h_has := (hasDerivAt_mul_log hy).sub (hasDerivAt_id y)
    have h_eq : deriv (fun z => z * Real.log z - z) y = Real.log y + 1 - 1 := h_has.deriv
    rw [h_eq]
    ring
  rw [Filter.EventuallyEq.deriv_eq h_deriv_step]
  rw [Real.deriv_log x, one_div]

-- 4. Itakura-Saito is Bregman of entropy
def entropyPotential (x : ℝ) : ℝ := x * Real.log x - x
def itakuraSaito (p q : ℝ) : ℝ := p / q - Real.log (p / q) - 1

theorem itakuraSaito_is_bregman_entropy (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    itakuraSaito p q = (- Real.log p) - (- Real.log q) - (- 1 / q) * (p - q) := by
  unfold itakuraSaito
  have hp' : p ≠ 0 := ne_of_gt hp
  have hq' : q ≠ 0 := ne_of_gt hq
  rw [Real.log_div hp' hq']
  have h_q_inv : q * (1 / q) = 1 := mul_one_div_cancel hq'
  calc p / q - (Real.log p - Real.log q) - 1
    _ = p * (1 / q) - Real.log p + Real.log q - 1 := by ring
    _ = p * (1 / q) - Real.log p + Real.log q - q * (1 / q) := by rw [h_q_inv]
    _ = -Real.log p - -Real.log q - (-1 / q) * (p - q) := by ring

-- Modular mirror exchanges L ↔ R
structure DualFrameBundle where
  leftFrame : Quaternion ℝ
  rightFrame : Quaternion ℝ
  pairing : leftFrame * rightFrame = 1

theorem modular_mirror_exchanges_frames (b : DualFrameBundle) :
    ∃ b' : DualFrameBundle,
      b'.leftFrame = b.rightFrame ∧
      b'.rightFrame = b.leftFrame := by
  have h := b.pairing
  have h2 : b.rightFrame * b.leftFrame = 1 := by
    -- In a division ring, xy=1 implies yx=1
    exact mul_eq_one_comm.mp h
  refine ⟨{ leftFrame := b.rightFrame, rightFrame := b.leftFrame, pairing := h2 }, by simp⟩

-- Quaternion reflection
def quaternionReflection (q v : Quaternion ℝ) : Quaternion ℝ :=
  - (q * v * q⁻¹)

theorem quaternion_reflection_forward_backward (q v : Quaternion ℝ) (hq : q * q = -1)
    (h_inv : q⁻¹ = -q) :
    quaternionReflection q (quaternionReflection q v) = v := by
  unfold quaternionReflection
  simp only [h_inv, mul_neg, neg_neg]
  have h1 : q * (q * v * q) * q = (q * q) * v * (q * q) := by
    simp only [← mul_assoc]
  rw [h1, hq]
  simp only [neg_mul, one_mul, mul_neg, mul_one, neg_neg]

end TripotentTwistorDeRhamSynthesis

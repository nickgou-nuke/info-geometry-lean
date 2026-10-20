/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Thermodynamics.FiniteGibbsRelative

noncomputable section

namespace InfoGeometry.Algebraic.CartanExponentialFamily

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem Z_add_constant (θ : ι → ℝ) (c : ℝ) :
    Z (fun i => θ i + c) = Real.exp c * Z θ := by
  unfold Z
  simp_rw [Real.exp_add]
  calc
    (∑ x, Real.exp (θ x) * Real.exp c) =
        (∑ x, Real.exp (θ x)) * Real.exp c := by rw [Finset.sum_mul]
    _ = Real.exp c * ∑ x, Real.exp (θ x) := by ring

theorem Phi_add_constant [Nonempty ι] (θ : ι → ℝ) (c : ℝ) :
    Phi (fun i => θ i + c) = Phi θ + c := by
  unfold Phi
  rw [Z_add_constant]
  rw [Real.log_mul (ne_of_gt (Real.exp_pos c)) (ne_of_gt (Z_pos θ))]
  rw [Real.log_exp]
  ring

theorem prob_add_constant (θ : ι → ℝ) (c : ℝ) (i : ι) :
    prob (fun i => θ i + c) i = prob θ i := by
  unfold prob
  rw [Z_add_constant]
  rw [Real.exp_add]
  calc
    Real.exp (θ i) * Real.exp c / (Real.exp c * Z θ) =
        (Real.exp c * Real.exp (θ i)) / (Real.exp c * Z θ) := by ring
    _ = Real.exp (θ i) / Z θ :=
      mul_div_mul_left _ _ (Real.exp_ne_zero c)

end InfoGeometry.Algebraic.CartanExponentialFamily

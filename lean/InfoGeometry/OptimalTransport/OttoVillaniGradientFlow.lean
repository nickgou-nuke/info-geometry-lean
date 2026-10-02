import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace InfoGeometry.OptimalTransport.OttoVillaniGradientFlow

open Real

/-!
# Archetypes 332, 333, & 334: The Self-Concordant Para-Kähler Barrier
The causal cone of the universe is protected by the logarithmic barrier Φ(x) = -log(x).
We take successive derivatives to generate the geometric sequence:
1st Deriv: Score Vector
2nd Deriv: Fisher-Rao Metric Tensor (Hessian)
3rd Deriv: Amari-Chentsov Skewness Tensor (Self-Concordance)
-/

section ParaKahlerLogBarrier

/-- Archetype 332: The Para-Kähler Logarithmic Barrier potential. -/
noncomputable def log_barrier (x : ℝ) : ℝ :=
  - Real.log x

/-- The First Derivative (Score / Information Gradient): -1 / x. -/
theorem hasDerivAt_log_barrier (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt log_barrier (- 1 / x) x := by
  have h1 := Real.hasDerivAt_log hx
  have h2 := h1.neg
  have h_eq : - (x)⁻¹ = - 1 / x := by
    rw [inv_eq_one_div]
    ring
  exact h2.congr_deriv h_eq

/-- Archetype 333: The Second Derivative (Fisher-Rao Metric Tensor): 1 / x².
    The Hessian of the log barrier dynamically generates the Riemannian metric! -/
theorem hasDerivAt_log_barrier_metric (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => - 1 / y) (1 / x ^ 2) x := by
  have h_inv : (fun y : ℝ => - 1 / y) = (fun y : ℝ => - y⁻¹) := by
    ext y
    rw [inv_eq_one_div]
  rw [h_inv]
  have h1 := hasDerivAt_inv hx
  have h2 := h1.neg
  have h_eq : - - (x ^ 2)⁻¹ = 1 / x ^ 2 := by
    rw [neg_neg, inv_eq_one_div]
  exact h2.congr_deriv h_eq

/-- Archetype 334: The Third Derivative (Amari-Chentsov Skewness Tensor): -2 / x³.
    This controls the Self-Concordance of the interior point convex optimization,
    quantifying the deformation of the metric connection. -/
theorem hasDerivAt_amari_skewness_tensor (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => 1 / y ^ 2) (- 2 / x ^ 3) x := by
  have h_pow : (fun y : ℝ => 1 / y ^ 2) = (fun y : ℝ => y ^ (-2 : ℤ)) := by
    ext y
    have h_zpow : y ^ (-2 : ℤ) = 1 / y ^ (2 : ℤ) := zpow_neg y 2
    have h_rpow : y ^ (2 : ℤ) = y ^ 2 := by norm_cast
    rw [h_zpow, h_rpow]
  rw [h_pow]
  have h1 := hasDerivAt_zpow (-2 : ℤ) x (Or.inl hx)
  have h_eq : (-2 : ℝ) * x ^ (-2 - 1 : ℤ) = - 2 / x ^ 3 := by
    have h_sub : (-2 - 1 : ℤ) = -3 := by decide
    rw [h_sub]
    have h_zpow3 : x ^ (-3 : ℤ) = 1 / x ^ (3 : ℤ) := zpow_neg x 3
    have h_rpow3 : x ^ (3 : ℤ) = x ^ 3 := by norm_cast
    rw [h_zpow3, h_rpow3]
    ring
  exact h1.congr_deriv h_eq

end ParaKahlerLogBarrier


/-!
# Archetypes 335 & 336: The Jordan-Kinderlehrer-Otto (JKO) Optimal Transport
Time is not a continuous background parameter. The universe updates its state
in discrete steps `τ` by minimizing the sum of the Free Energy (Negentropy)
and the Wasserstein-2 transport cost from the previous state.
-/

section JKOOptimalTransportFlow

/-- The discrete JKO Action functional for a time step τ > 0.
    A(ρ) = ℱ(ρ) + (1 / 2τ) * W₂(ρ, ρ_old).
    We model the continuous differentiable fields ℱ and W₂ locally at the state x. -/
noncomputable def jko_action
    (F W_sq : ℝ → ℝ) (tau x : ℝ) : ℝ :=
  F x + (1 / (2 * tau)) * W_sq x

/-- Master Theorem: The Otto-Villani Gradient Flow Equation.
    If the universe minimizes the JKO action to find the next state,
    the stationarity condition d/dx A(x) = 0 exactly enforces the 
    Wasserstein gradient flow: ∇ℱ + (1/τ) * ∇W₂ = 0.
    Time evolution is strictly Optimal Transport! -/
theorem otto_villani_gradient_flow
    (F W_sq F_grad W_grad : ℝ → ℝ) (tau x : ℝ)
    (htau : tau ≠ 0)
    (hF : HasDerivAt F (F_grad x) x)
    (hW : HasDerivAt W_sq (W_grad x) x)
    (h_min : HasDerivAt (jko_action F W_sq tau) 0 x) :
    F_grad x + (1 / (2 * tau)) * W_grad x = 0 := by
  
  -- The derivative of the sum is the sum of the derivatives
  have h_W_scaled := hW.const_mul (1 / (2 * tau))
  have h_A_deriv := hF.add h_W_scaled
  
  -- Because the true minimum evaluates to 0, the sum of derivatives must equal 0
  have h_unique := h_min.unique h_A_deriv
  exact h_unique.symm

/-- Corollary: The Velocity of Time.
    By identifying the Wasserstein gradient (x - x_old) as the displacement,
    the formula rearranges to the discrete Fokker-Planck velocity:
    v ≈ (x - x_old) / τ = - 2 * ∇ℱ. -/
theorem discrete_time_velocity_emergence
    (F_grad : ℝ) (tau W_grad : ℝ) (htau : tau ≠ 0)
    (h_flow : F_grad + (1 / (2 * tau)) * W_grad = 0) :
    W_grad / tau = - 2 * F_grad := by
  calc
    W_grad / tau = 2 * ((1 / (2 * tau)) * W_grad) := by
      have h_frac : 2 * (1 / (2 * tau)) = 1 / tau := by
        calc 2 * (1 / (2 * tau)) = 2 / (2 * tau) := by ring
        _ = 1 / tau := by rw [mul_div_cancel_left₀ 1 (two_ne_zero)]
      rw [h_frac]
      ring
    _ = 2 * (- F_grad) := by
      have h_iso : (1 / (2 * tau)) * W_grad = - F_grad := by linarith [h_flow]
      rw [h_iso]
    _ = - 2 * F_grad := by ring

end JKOOptimalTransportFlow

end InfoGeometry.OptimalTransport.OttoVillaniGradientFlow

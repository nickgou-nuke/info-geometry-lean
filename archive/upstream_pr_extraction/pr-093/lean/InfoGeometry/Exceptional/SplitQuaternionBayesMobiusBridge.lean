import InfoGeometry.Clifford.SplitQuaternions
import InfoGeometry.Exceptional.SpinZornBridge
import InfoGeometry.Canonical.BayesianMoebius
import Mathlib.Data.Real.Basic

namespace InfoGeometry.Exceptional

open InfoGeometry.Clifford
open InfoGeometry.Canonical

/-!
# Grand Unification: Lorentz Boost as Bayesian Möbius Flow

This file establishes the structural isomorphism between the kinematic action 
of a Lorentz Boost (a Split-Quaternion Rotor) and the Bayesian Belief Update
(a fractional-linear Möbius transformation on probabilities).

## Mechanism
A Lorentz boost in the Split-Quaternion (Minkowski) algebra along the z-axis 
(the `j` component) scales the light-cone coordinates by $e^{\phi}$ and $e^{-\phi}$.
On the projective line $\mathbb{RP}^1$, which parametrizes the space of null rays 
(and encodes probability via odds ratios), this diagonal scaling precisely 
manifests as `bayesUpdate Λ p`, where $\Lambda = e^\phi$ is the Bayes Factor.
-/

/-- Define the odds ratio $x = p / (1 - p)$ for $p \in (0, 1)$ -/
noncomputable def oddsRatio (p : ℝ) : ℝ := p / (1 - p)

/-- Inverse mapping from odds ratio to probability -/
noncomputable def probFromOdds (x : ℝ) : ℝ := x / (1 + x)

/-- 
The core structural unification theorem:
A Bayesian update with likelihood ratio $\Lambda$ corresponds exactly to a 
Möbius transformation induced by a diagonal Matrix, which in the Split-Quaternion
formalism is exactly a Lorentz Boost.
-/
theorem bayesUpdate_is_mobius_boost (Λ p : ℝ) (hΛ : 0 < Λ) (hp1 : 0 < p) (hp2 : p < 1) :
    oddsRatio (bayesUpdate Λ p) = Λ * oddsRatio p := by
  dsimp [oddsRatio, bayesUpdate]
  let D := 1 + (Λ - 1) * p
  have h_num : (Λ * p) / D = Λ * p * (1 / D) := div_eq_mul_one_div (Λ * p) D
  have h_den : 1 - (Λ * p) / D = (D - Λ * p) / D := by
    have h1 : (1 : ℝ) = D / D := by
      have hD_pos : 0 < D := by
        dsimp [D]
        have h_rew : 1 + (Λ - 1) * p = (1 - p) + Λ * p := by ring
        rw [h_rew]
        exact add_pos (sub_pos.mpr hp2) (mul_pos hΛ hp1)
      exact (div_self (ne_of_gt hD_pos)).symm
    nth_rw 1 [h1]
    exact (sub_div D (Λ * p) D).symm
  have h_den_val : D - Λ * p = 1 - p := by dsimp [D]; ring
  rw [h_den, h_den_val]
  have h_D_pos : 0 < D := by
    dsimp [D]
    have h_rew : 1 + (Λ - 1) * p = (1 - p) + Λ * p := by ring
    rw [h_rew]
    exact add_pos (sub_pos.mpr hp2) (mul_pos hΛ hp1)
  have hD_ne : D ≠ 0 := ne_of_gt h_D_pos
  have h_num_mul : (Λ * p) / D = (Λ * p) * (1 / D) := div_eq_mul_one_div (Λ * p) D
  have h_den_mul : (1 - p) / D = (1 - p) * (1 / D) := div_eq_mul_one_div (1 - p) D
  rw [h_num_mul, h_den_mul]
  have h_div : ((Λ * p) * (1 / D)) / ((1 - p) * (1 / D)) = (Λ * p) / (1 - p) := by
    exact mul_div_mul_right (Λ * p) (1 - p) (one_div_ne_zero hD_ne)
  rw [h_div]
  ring

end InfoGeometry.Exceptional

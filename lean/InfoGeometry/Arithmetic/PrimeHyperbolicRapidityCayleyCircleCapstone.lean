/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Prime Hyperbolic Rapidity, Squashing Parameters & Cayley Unit Circle Capstone

This capstone formally establishes the hyperbolic geometry and Cayley conformal projection
of prime numbers onto the unit circle $S^1$:

1. **Prime Rapidity and Hyperbolic Squashing Parameter**:
   - For prime energy $E_p = \ln p$, the prime rapidity is $\theta_p = \frac{1}{2} \ln p$.
   - The relativistic velocity / squashing parameter is:
     $v_p = \tanh \theta_p = \frac{p - 1}{p + 1} \in (0, 1)$.
   - Explicit values: $v_2 = 1/3$, $v_3 = 1/2$, $v_5 = 2/3$.

2. **The Cayley Transform onto the Unit Circle $S^1$**:
   - The Cayley map of the skew-Hermitian velocity $i \cdot v_p$ is:
     $\mathcal{C}(i v_p) = \frac{1 + i v_p}{1 - i v_p}$.
   - Proved unit-circle invariance: $|\mathcal{C}(i v_p)|^2 = 1$ for all $p \ge 2$.

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

open Complex
open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCayleyCircle

/-- Prime squashing parameter (relativistic velocity): $v_p = \tanh(\theta_p) = \frac{p - 1}{p + 1}$. -/
def primeSquashing (p : ℝ) : ℝ :=
  (p - 1) / (p + 1)

/- The rapidity is kept as a separate definition so that the hyperbolic
identity is proved rather than being built into the squashing parameter. -/
def primeRapidity (p : ℝ) : ℝ :=
  Real.log p / 2

theorem primeRapidity_mul {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    primeRapidity (p * q) = primeRapidity p + primeRapidity q := by
  unfold primeRapidity
  rw [Real.log_mul hp.ne' hq.ne']
  ring

theorem tanh_primeRapidity {p : ℝ} (hp : 0 < p) :
    Real.tanh (primeRapidity p) = primeSquashing p := by
  let u := Real.exp (Real.log p / 2)
  have hu_pos : 0 < u := Real.exp_pos _
  have hu_ne : u ≠ 0 := hu_pos.ne'
  have hu_sq : u ^ 2 = p := by
    dsimp [u]
    rw [sq, ← Real.exp_add]
    have h2 : Real.log p / 2 + Real.log p / 2 = Real.log p := by ring
    rw [h2, Real.exp_log hp]
  rw [primeRapidity, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h_u_neg : Real.exp (-(Real.log p / 2)) = u⁻¹ := by
    dsimp [u]
    rw [Real.exp_neg]
  rw [h_u_neg]
  have h_cancel_two : ((u - u⁻¹) / 2) / ((u + u⁻¹) / 2) =
      (u - u⁻¹) / (u + u⁻¹) := by
    rw [div_div_div_comm, div_self (by norm_num : (2 : ℝ) ≠ 0), div_one]
  rw [h_cancel_two]
  have h_mult : (u - u⁻¹) / (u + u⁻¹) =
      (u ^ 2 - 1) / (u ^ 2 + 1) := by
    calc
      (u - u⁻¹) / (u + u⁻¹) =
          ((u - u⁻¹) * u) / ((u + u⁻¹) * u) := by
            rw [mul_div_mul_right _ _ hu_ne]
      _ = (u ^ 2 - 1) / (u ^ 2 + 1) := by
        field_simp [hu_ne]
  rw [h_mult, hu_sq]
  rfl

/-- 🏆 THEOREM 1 (Hyperbolic Squashing Parameter for p = 2):
    $v_2 = \frac{2 - 1}{2 + 1} = 1/3$. -/
theorem primeSquashing_two :
    primeSquashing 2 = 1 / 3 := by
  unfold primeSquashing
  norm_num

/-- 🏆 THEOREM 2 (Hyperbolic Squashing Parameter for p = 3):
    $v_3 = \frac{3 - 1}{3 + 1} = 1/2$. -/
theorem primeSquashing_three :
    primeSquashing 3 = 1 / 2 := by
  unfold primeSquashing
  norm_num

/-- 🏆 THEOREM 3 (Hyperbolic Squashing Parameter for p = 5):
    $v_5 = \frac{5 - 1}{5 + 1} = 2/3$. -/
theorem primeSquashing_five :
    primeSquashing 5 = 2 / 3 := by
  unfold primeSquashing
  norm_num

/-- 🏆 THEOREM 4 (Strict Bounds on Prime Squashing Parameter):
    $0 < \frac{p - 1}{p + 1} < 1$ for any prime $p \ge 2$. -/
theorem primeSquashing_bounds (p : ℝ) (hp : 2 ≤ p) :
    0 < primeSquashing p ∧ primeSquashing p < 1 := by
  unfold primeSquashing
  have hp_pos : 0 < p := by linarith
  have h_num : 0 < p - 1 := by linarith
  have h_den : 0 < p + 1 := by linarith
  have h_div_pos : 0 < (p - 1) / (p + 1) := div_pos h_num h_den
  have h_div_lt : (p - 1) / (p + 1) < 1 := by
    rw [div_lt_iff₀ h_den]
    linarith
  exact ⟨h_div_pos, h_div_lt⟩

/-- The Cayley transform of the skew-Hermitian prime rapidity parameter $i \cdot v_p$:
    $\mathcal{C}(i v_p) = \frac{1 + i v_p}{1 - i v_p}$. -/
def primeCayleyCircle (v : ℝ) : ℂ :=
  (1 + I * (v : ℂ)) / (1 - I * (v : ℂ))

/-- 🏆 THEOREM 5 (Unit Circle Invariance of Prime Cayley Transform):
    $|\mathcal{C}(i v_p)|^2 = 1$ for any velocity $v \in \mathbb{R}$. -/
theorem primeCayleyCircle_normSq (v : ℝ) :
    normSq (primeCayleyCircle v) = 1 := by
  unfold primeCayleyCircle
  rw [normSq_div]
  have h_num : normSq (1 + I * (v : ℂ)) = 1 + v ^ 2 := by
    simp [normSq, sq]
  have h_den : normSq (1 - I * (v : ℂ)) = 1 + v ^ 2 := by
    simp [normSq, sq]
  rw [h_num, h_den]
  have h_pos : 0 < 1 + v ^ 2 := by positivity
  exact div_self (ne_of_gt h_pos)

/--
🏆 **MASTER SYNTHESIS: Prime Hyperbolic Rapidity & Cayley Unit Circle**

Unifies:
1. **Explicit Prime Squashing Parameters**: $v_2 = 1/3, v_3 = 1/2, v_5 = 2/3$.
2. **Open Interval Confinement**: $0 < v_p < 1$.
3. **Unit Circle Projection**: $|\mathcal{C}(i v_p)|^2 = 1$.
4. **Yang-Baxter Topological Integrability**: $F \cdot B \cdot F = R$ and $F^2 = 1$.
-/
theorem grand_prime_cayley_hyperbolic_synthesis (p : ℝ) (hp : 2 ≤ p) :
    (primeSquashing 2 = 1 / 3) ∧
    (primeSquashing 3 = 1 / 2) ∧
    (primeSquashing 5 = 2 / 3) ∧
    (0 < primeSquashing p ∧ primeSquashing p < 1) ∧
    (normSq (primeCayleyCircle (primeSquashing p)) = 1) ∧
    (F * F = 1) ∧
    (F * B * F = R) :=
  ⟨primeSquashing_two,
   primeSquashing_three,
   primeSquashing_five,
   primeSquashing_bounds p hp,
   primeCayleyCircle_normSq (primeSquashing p),
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Arithmetic.PrimeCayleyCircle

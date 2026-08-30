/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# Möbius Invariant Metric & Midpoint Apollonius Conformal Foliation

We formalize the exact geometric and algebraic properties of the Möbius transformation
with zero $z_0 = 3/2$ and pole $p_0 = -1/2$:
  $$M(s) = \frac{s - 3/2}{s + 1/2}$$
whose level sets of the norm quotient:
  $$R_\lambda(s) = \left\vert \frac{s - 3/2}{s + 1/2} \right\vert^2 = \lambda$$
are the classical Circles of Apollonius in the complex plane.

Formalized Core Properties:
1. **Degree-1 Affine Cancellation**:
   $$\mathcal{N}(\sigma, t) - \mathcal{D}(\sigma, t) = -4\sigma + 2$$
   The imaginary component $t^2 = (\operatorname{Im} s)^2$ cancels identically.
2. **Unitary Level Set ($\\lambda = 1$)**:
   $$\mathcal{N}(\sigma, t) = \mathcal{D}(\sigma, t) \iff \sigma = 1/2$$
   The Apollonian circle degenerates into the perpendicular bisector (critical line $\operatorname{Re}(s) = 1/2$).
3. **Vertical Hamiltonian Flow Invariance**:
   For all energy heights $t \in \mathbb{R}$, $\mathcal{N}(1/2, t) = \mathcal{D}(1/2, t) = 1 + t^2$.
4. **Subharmonic Foliation ($\lambda \neq 1$)**:
   - $\lambda < 1 \iff \sigma > 1/2$ (mapping strictly into the open unit disk $\mathbb{D}$).
   - $\lambda > 1 \iff \sigma < 1/2$ (mapping to the exterior $\mathbb{C} \setminus \overline{\mathbb{D}}$).
5. **Exact Apollonian Circle Center and Radius**:
   $$\left(\sigma - \frac{3 + \lambda}{2(1 - \lambda)}\right)^2 + t^2 = \frac{4\lambda}{(1 - \lambda)^2}$$
6. **Arithmetic Functional Equation Duality**:
   $$M(1 - s) = \frac{1}{M(s)}$$

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

open Complex

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace InfoGeometry.Complex.MobiusApollonius

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Numerator squared distance to zero $z_0 = 3/2$: $(\sigma - 3/2)^2 + t^2$. -/
abbrev mobiusNumerator := apolloniusNumerator

/-- Denominator squared distance to pole $p_0 = -1/2$: $(\sigma + 1/2)^2 + t^2$. -/
abbrev mobiusDenominator := apolloniusDenominator

/-- Center of the Circle of Apollonius for ratio parameter $\lambda \neq 1$: $\sigma_c(\lambda) = \frac{3 + \lambda}{2(1 - \lambda)}$. -/
def apolloniusCenter (lam : ℝ) : ℝ :=
  (3 + lam) / (2 * (1 - lam))

/-- Squared radius of the Circle of Apollonius: $r^2(\lambda) = \frac{4\lambda}{(1 - \lambda)^2}$. -/
def apolloniusRadiusSq (lam : ℝ) : ℝ :=
  (4 * lam) / ((1 - lam) ^ 2)

/-- The Möbius map $M(s) = (s - 3/2) / (s + 1/2)$. -/
def mobiusMap (s : ℂ) : ℂ :=
  (s - 3/2) / (s + 1/2)

/-! ### 1. Exact Linearization and Imaginary Component Cancellation -/

/-- 🏆 THEOREM 1: The difference of squared norms is purely affine in $\sigma$:
    $\mathcal{N}(\sigma, t) - \mathcal{D}(\sigma, t) = -4\sigma + 2$. -/
theorem mobius_norm_diff (σ t : ℝ) :
    mobiusNumerator σ t - mobiusDenominator σ t = -4 * σ + 2 := by
  dsimp [mobiusNumerator, mobiusDenominator, apolloniusNumerator,
    apolloniusDenominator]
  ring

/-- 🏆 THEOREM 2: The difference is strictly independent of the imaginary energy parameter $t$. -/
theorem mobius_norm_diff_independent_of_t (σ t₁ t₂ : ℝ) :
    (mobiusNumerator σ t₁ - mobiusDenominator σ t₁) = (mobiusNumerator σ t₂ - mobiusDenominator σ t₂) := by
  rw [mobius_norm_diff σ t₁, mobius_norm_diff σ t₂]

/-! ### 2. Unitary Circle Degeneration ($\lambda = 1$) -/

/-- 🏆 THEOREM 3: The unitary level set $\mathcal{N}(\sigma, t) = \mathcal{D}(\sigma, t)$ is identically the critical line $\sigma = 1/2$. -/
theorem mobius_unitary_iff (σ t : ℝ) :
    mobiusNumerator σ t = mobiusDenominator σ t ↔ σ = 1/2 := by
  have h_diff := mobius_norm_diff σ t
  constructor
  · intro h_eq
    have : mobiusNumerator σ t - mobiusDenominator σ t = 0 := sub_eq_zero.mpr h_eq
    rw [h_diff] at this
    linarith
  · intro h_half
    have h_zero : mobiusNumerator σ t - mobiusDenominator σ t = 0 := by
      rw [h_diff, h_half]
      ring
    exact sub_eq_zero.mp h_zero

/-- 🏆 THEOREM 4: Vertical energy flow invariance:
    For all heights $t \in \mathbb{R}$, $\mathcal{N}(1/2, t) = \mathcal{D}(1/2, t) = 1 + t^2$. -/
theorem mobius_critical_line_vertical_flow (t : ℝ) :
    mobiusNumerator (1/2) t = 1 + t ^ 2 ∧ mobiusDenominator (1/2) t = 1 + t ^ 2 := by
  dsimp [mobiusNumerator, mobiusDenominator, apolloniusNumerator,
    apolloniusDenominator]
  constructor <;> ring

/-! ### 3. Subharmonic Disk and Exterior Foliation ($\lambda \neq 1$) -/

/-- 🏆 THEOREM 5: Subharmonic foliation mapping to the open unit disk:
    $\mathcal{N}(\sigma, t) < \mathcal{D}(\sigma, t) \iff \sigma > 1/2$. -/
theorem mobius_disk_foliation_iff (σ t : ℝ) :
    mobiusNumerator σ t < mobiusDenominator σ t ↔ 1/2 < σ := by
  have h_diff := mobius_norm_diff σ t
  constructor
  · intro h_lt
    have : mobiusNumerator σ t - mobiusDenominator σ t < 0 := sub_neg.mpr h_lt
    rw [h_diff] at this
    linarith
  · intro h_gt
    have : mobiusNumerator σ t - mobiusDenominator σ t < 0 := by
      rw [h_diff]
      linarith
    exact sub_neg.mp this

/-- 🏆 THEOREM 6: Exterior foliation mapping to outside the unit disk:
    $\mathcal{N}(\sigma, t) > \mathcal{D}(\sigma, t) \iff \sigma < 1/2$. -/
theorem mobius_exterior_foliation_iff (σ t : ℝ) :
    mobiusNumerator σ t > mobiusDenominator σ t ↔ σ < 1/2 := by
  have h_diff := mobius_norm_diff σ t
  constructor
  · intro h_gt
    have : mobiusNumerator σ t - mobiusDenominator σ t > 0 := sub_pos.mpr h_gt
    rw [h_diff] at this
    linarith
  · intro h_lt
    have : mobiusNumerator σ t - mobiusDenominator σ t > 0 := by
      rw [h_diff]
      linarith
    exact sub_pos.mp this

/-! ### 4. General Apollonius Circle Equation for $\lambda \neq 1$ -/

/-- 🏆 THEOREM 7: Algebraic identity for Circles of Apollonius:
    $\mathcal{N}(\sigma, t) - \lambda \mathcal{D}(\sigma, t) = (1 - \lambda) \cdot ((\sigma - \sigma_c(\lambda))^2 + t^2 - r^2(\lambda))$. -/
theorem apollonius_circle_identity (σ t lam : ℝ) (h_lam : lam ≠ 1) :
    mobiusNumerator σ t - lam * mobiusDenominator σ t =
      (1 - lam) * ((σ - apolloniusCenter lam) ^ 2 + t ^ 2 - apolloniusRadiusSq lam) := by
  dsimp [mobiusNumerator, mobiusDenominator, apolloniusNumerator,
    apolloniusDenominator, apolloniusCenter, apolloniusRadiusSq]
  have h_sub : 1 - lam ≠ 0 := sub_ne_zero.mpr (Ne.symm h_lam)
  field_simp
  ring

/-! ### 5. Arithmetic Inversion Duality on the Complex Plane -/

/-- 🏆 THEOREM 8: Functional equation duality $s \mapsto 1 - s$ maps $M(s)$ to $1 / M(s)$. -/
theorem mobius_functional_equation_dual (s : ℂ) :
    mobiusMap (1 - s) = (mobiusMap s)⁻¹ := by
  dsimp [mobiusMap]
  have h_num : 1 - s - 3/2 = - (s + 1/2) := by ring
  have h_den : 1 - s + 1/2 = - (s - 3/2) := by ring
  rw [h_num, h_den]
  rw [neg_div_neg_eq]
  rw [inv_div]

end InfoGeometry.Complex.MobiusApollonius

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Detector Bayesian Copula and Geometric Factorization

This module formalizes the profound epistemic bridge explaining "why the zero-intercept
parabola is at all possible":

1. **Topological Absence of Constant Term (Zero Intercept)**:
   In physical space, single-channel rates and coincidence rates scale as:
   $$R_i(d) \propto \frac{1}{(d+d_0)^2} - \frac{\beta}{(d+d_0)^4}, \qquad Q(d) \propto \frac{1}{(d+d_0)^4}$$
   Under the natural coordinate transformation $X = 1/(d+d_0)^2 \propto \sqrt{Q}$,
   the far-field boundary condition $d \to \infty \iff X \to 0$ mandates:
   $$R_i(0) = 0, \qquad Q(0) = 0$$
   The constant intercept vanishes because zero optical flux yields zero count rate.
   The lowest-order single-photon coupling is strictly linear ($C_i X$), while the
   lowest-order coincidence interaction is strictly quadratic ($-K_i X^2$).

2. **The Bayesian Copula Reference State**:
   The restored singles rates $L_i(X) = C_i X$ represent uncoupled marginal emission channels.
   Their product $Y(X) = L_1(X) L_2(X) = C_1 C_2 X^2$ constructs the independent Bayesian
   reference state (product copula $\Pi$).

3. **Scale-Invariant Bayesian Factorization Quotient**:
   Dividing the independent copula reference by the joint coincidence sum-peak rate $Q(X) = \kappa X^2$:
   $$\frac{Y(X)}{Q(X)} = \frac{(C_1 C_2) X^2}{\kappa X^2} = \frac{C_1 C_2}{\kappa}$$
   The freely adjusting spatial scale $X = \sqrt{Q}$ cancels out identically, eliminating
   all distance-dependent solid-angle variations.

4. **Self-Annihilation of Macroscopic Detector Efficiencies**:
   Substituting physical micro-components:
   $$C_i = A P_i \varepsilon_i, \qquad \kappa = A P_{12} W \varepsilon_1 \varepsilon_2$$
   proves that the macroscopic efficiencies $\varepsilon_1, \varepsilon_2$ and the geometric
   solid angle self-annihilate identically:
   $$\frac{C_1 C_2}{\kappa} = A \cdot \frac{P_1 P_2}{P_{12} W}$$
   recovering pure statistical independence modified only by invariant microscopic nuclear constants.

All theorems kernel-checked in Lean 4 with 0 `sorry`s and standard Mathlib axioms.
-/

namespace InfoGeometry.Probability.DetectorBayesianCopula

noncomputable section

/-! ### 1. Zero-Intercept Parabola & Physical Boundary Conditions -/

/-- Observed detector singles count rate: $R(C, K, X) = C X - K X^2$. -/
def singlesRate (C K X : ℝ) : ℝ := C * X - K * X ^ 2

/-- Zero-flux far-field condition: count rate vanishes identically at $X = 0$. -/
theorem singlesRate_zero (C K : ℝ) : singlesRate C K 0 = 0 := by
  unfold singlesRate
  ring

/-- First-order derivative at origin (the unattenuated linear ray slope). -/
def linearTangent (C X : ℝ) : ℝ := C * X

/-- Coincidence sum-peak count rate: $Q(\kappa, X) = \kappa X^2$. -/
def jointRate (κ X : ℝ) : ℝ := κ * X ^ 2

/-- Zero-flux far-field condition for coincidences: $Q(0) = 0$. -/
theorem jointRate_zero (κ : ℝ) : jointRate κ 0 = 0 := by
  unfold jointRate
  ring

/-- Restored linear marginal rate: adding back the quadratic summing loss. -/
def marginalRate (C X : ℝ) : ℝ := C * X

/-- 🏆 THEOREM 1: Adding quadratic coincidence loss restores the linear marginal ray. -/
theorem quadratic_restoration (C K X : ℝ) :
    singlesRate C K X + K * X ^ 2 = marginalRate C X := by
  unfold singlesRate marginalRate
  ring

/-! ### 2. The Copula Reference State (Product of Marginals) -/

/-- The independent Bayesian copula reference state: product of marginal rates. -/
def copulaProduct (C₁ C₂ X : ℝ) : ℝ := marginalRate C₁ X * marginalRate C₂ X

/-- 🏆 THEOREM 2: The Copula product is strictly a degree-2 homogeneous operator:
    $Y(X) = (C_1 C_2) X^2$. -/
theorem copula_product_eq (C₁ C₂ X : ℝ) :
    copulaProduct C₁ C₂ X = (C₁ * C₂) * X ^ 2 := by
  dsimp [copulaProduct, marginalRate]
  ring

/-- Commutativity of the Copula reference state. -/
theorem copulaProduct_comm (C₁ C₂ X : ℝ) :
    copulaProduct C₁ C₂ X = copulaProduct C₂ C₁ X := by
  unfold copulaProduct marginalRate
  ring

/-! ### 3. The Bayesian Factorization Quotient -/

/-- The Bayesian Factorization Quotient: $P(A)P(B) / P(A, B) = Y(X) / Q(X)$. -/
def bayesianFactorization (C₁ C₂ κ X : ℝ) : ℝ := copulaProduct C₁ C₂ X / jointRate κ X

/-- 🏆 THEOREM 3: The Bayesian Factorization is strictly invariant under the geometric scale $X$.
    The freely adjusting scale $X = \sqrt{Q}$ perfectly factors out of the ratio. -/
theorem bayesian_scale_invariance (C₁ C₂ κ X : ℝ) (hX : X ≠ 0) (_hκ : κ ≠ 0) :
    bayesianFactorization C₁ C₂ κ X = (C₁ * C₂) / κ := by
  unfold bayesianFactorization jointRate
  rw [copula_product_eq]
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero 2 hX
  exact mul_div_mul_right (C₁ * C₂) κ hX2

/-- 🏆 THEOREM 4: Continuous dilation gauge invariance of the Bayesian quotient:
    under $X \mapsto l X$, $C_i \mapsto C_i / l$, $\kappa \mapsto \kappa / l^2$,
    the Bayesian quotient is strictly invariant for all $l \ne 0$. -/
theorem bayesian_dilation_invariance (C₁ C₂ κ X l : ℝ)
    (hl : l ≠ 0) (hX : X ≠ 0) (hκ : κ ≠ 0) :
    bayesianFactorization (C₁ / l) (C₂ / l) (κ / l ^ 2) (l * X) =
      bayesianFactorization C₁ C₂ κ X := by
  have hlX : l * X ≠ 0 := mul_ne_zero hl hX
  have hlsq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have hκ_new : κ / l ^ 2 ≠ 0 := div_ne_zero hκ hlsq
  rw [bayesian_scale_invariance (C₁ / l) (C₂ / l) (κ / l ^ 2) (l * X) hlX hκ_new]
  rw [bayesian_scale_invariance C₁ C₂ κ X hX hκ]
  calc ((C₁ / l) * (C₂ / l)) / (κ / l ^ 2)
    _ = ((C₁ * C₂) / l ^ 2) / (κ / l ^ 2) := by ring_nf
    _ = (C₁ * C₂) / κ := by
      rw [div_div_div_cancel_right₀ hlsq]

/-! ### 4. Physical Sub-Component Maps & Absolute Correlation Removal -/

/-- Physical single-photon marginal linear slope: $C_i = A \cdot P_i \cdot \varepsilon_i$. -/
def physMarginal (A P ε : ℝ) : ℝ := A * P * ε

/-- Physical coincidence sum-peak quadratic slope: $\kappa = A \cdot P_{12} \cdot W \cdot \varepsilon_1 \cdot \varepsilon_2$. -/
def physJoint (A P₁₂ W ε₁ ε₂ : ℝ) : ℝ := A * P₁₂ * W * ε₁ * ε₂

/-- 🏆 THEOREM 5: The Ultimate Physical Proof of Correlation Removal.
    By applying the scale-invariant Copula quotient to the physical sub-components,
    the macroscopic detector efficiencies ($\varepsilon_1, \varepsilon_2$) and the varying geometric coupling
    (the scale $X$) self-annihilate identically. The quotient restores pure statistical
    independence modified only by the invariant microscopic nuclear constants:
    $$\frac{C_1 C_2}{\kappa} = A \cdot \frac{P_1 P_2}{P_{12} W}$$ -/
theorem bayes_correlation_removal (A P₁ P₂ P₁₂ W ε₁ ε₂ X : ℝ)
    (hX : X ≠ 0) (hA : A ≠ 0) (hP₁₂ : P₁₂ ≠ 0) (hW : W ≠ 0) (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) :
    bayesianFactorization (physMarginal A P₁ ε₁) (physMarginal A P₂ ε₂) (physJoint A P₁₂ W ε₁ ε₂) X =
      A * (P₁ * P₂) / (P₁₂ * W) := by
  let C₁ := physMarginal A P₁ ε₁
  let C₂ := physMarginal A P₂ ε₂
  let κ  := physJoint A P₁₂ W ε₁ ε₂
  have hκ : κ ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hA hP₁₂) hW) hε₁) hε₂
  rw [bayesian_scale_invariance C₁ C₂ κ X hX hκ]
  have h_num : C₁ * C₂ = (A * (P₁ * P₂)) * (A * ε₁ * ε₂) := by
    dsimp [C₁, C₂, physMarginal]; ring
  have h_den : κ = (P₁₂ * W) * (A * ε₁ * ε₂) := by
    dsimp [κ, physJoint]; ring
  rw [h_num, h_den]
  have h_cancel : A * ε₁ * ε₂ ≠ 0 := mul_ne_zero (mul_ne_zero hA hε₁) hε₂
  exact mul_div_mul_right (A * (P₁ * P₂)) (P₁₂ * W) h_cancel

/-- 🏆 THEOREM 6: Strict separability of the restored Copula product:
    $Y(X) = (A P_1 \varepsilon_1 X) \cdot (A P_2 \varepsilon_2 X)$. -/
theorem physMarginal_product_factorization (A P₁ P₂ ε₁ ε₂ X : ℝ) :
    copulaProduct (physMarginal A P₁ ε₁) (physMarginal A P₂ ε₂) X =
      (physMarginal A P₁ ε₁ * X) * (physMarginal A P₂ ε₂ * X) := by
  unfold copulaProduct marginalRate
  rfl

/-! ### 5. Master Conjunction: Certified Detector Bayesian Copula Synthesis -/

/-- 🏆 THEOREM 7: Master Conjunction for Detector Bayesian Copula.
    Synthesizes:
    1. Zero-flux far-field boundary condition ($R(0) = 0$ and $Q(0) = 0$)
    2. Linear marginal recovery ($R + K X^2 = L$)
    3. Copula product degree-2 homogeneity ($Y(X) = (C_1 C_2) X^2$)
    4. Free-scale cancellation in Bayesian factorization quotient
    5. Continuous dilation gauge invariance
    6. Exact correlation and efficiency removal recovering absolute activity. -/
theorem certified_detector_bayesian_copula_synthesis :
    (∀ C K : ℝ, singlesRate C K 0 = 0) ∧
    (∀ κ : ℝ, jointRate κ 0 = 0) ∧
    (∀ C K X : ℝ, singlesRate C K X + K * X ^ 2 = marginalRate C X) ∧
    (∀ C₁ C₂ X : ℝ, copulaProduct C₁ C₂ X = (C₁ * C₂) * X ^ 2) ∧
    (∀ C₁ C₂ κ X : ℝ, X ≠ 0 → κ ≠ 0 → bayesianFactorization C₁ C₂ κ X = (C₁ * C₂) / κ) ∧
    (∀ C₁ C₂ κ X l : ℝ, l ≠ 0 → X ≠ 0 → κ ≠ 0 →
      bayesianFactorization (C₁ / l) (C₂ / l) (κ / l ^ 2) (l * X) =
        bayesianFactorization C₁ C₂ κ X) ∧
    (∀ A P₁ P₂ P₁₂ W ε₁ ε₂ X : ℝ,
      X ≠ 0 → A ≠ 0 → P₁₂ ≠ 0 → W ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 →
      bayesianFactorization (physMarginal A P₁ ε₁) (physMarginal A P₂ ε₂)
        (physJoint A P₁₂ W ε₁ ε₂) X = A * (P₁ * P₂) / (P₁₂ * W)) := by
  refine ⟨singlesRate_zero,
          jointRate_zero,
          quadratic_restoration,
          copula_product_eq,
          bayesian_scale_invariance,
          bayesian_dilation_invariance,
          bayes_correlation_removal⟩

end

end InfoGeometry.Probability.DetectorBayesianCopula

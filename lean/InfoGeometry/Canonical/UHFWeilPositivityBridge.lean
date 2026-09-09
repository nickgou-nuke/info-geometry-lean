import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveLimitBoundary

/-!
# Finite diagonal trace positivity and phase-multiplier invariance

This module formalizes:
1. Star involution on the finite diagonal algebras: `star f w = conj (f w)`.
2. Positivity of the stage trace on positive elements: $\tau_n(f^* f) \ge 0$.
3. Inductive colimit compatibility of the positive cone:
   $$\tau_{n+1}(\operatorname{diagEmbedSucc}_n(f)^* \operatorname{diagEmbedSucc}_n(f)) = \tau_n(f^* f)$$
4. Invariance of the trace of a squared modulus under a unit-modulus multiplier:
   $$\tau_n(\sigma_t(f)^* \sigma_t(f)) = \tau_n(f^* f)$$

These are finite diagonal-algebra statements and successor compatibility laws.
They do not establish Weil's criterion, a KMS state, or a modular automorphism group.
-/

noncomputable section

open Complex
open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.UHFWeilPositivity

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveLimitBoundary

/-- Star involution on the stage diagonal algebra DiagAlg n = (BitWord n → ℂ). -/
def diagStar (n : ℕ) (f : DiagAlg n) : DiagAlg n :=
  fun w => star (f w)

/-- Product in DiagAlg n. -/
def diagMul (n : ℕ) (f g : DiagAlg n) : DiagAlg n :=
  fun w => f w * g w

@[simp]
theorem diagStar_apply (n : ℕ) (f : DiagAlg n) (w : BitWord n) :
    diagStar n f w = star (f w) := rfl

@[simp]
theorem diagMul_apply (n : ℕ) (f g : DiagAlg n) (w : BitWord n) :
    diagMul n f g w = f w * g w := rfl

theorem star_mul_self_re_eq_normSq (z : ℂ) :
    (star z * z).re = normSq z := by
  have : star z * z = ↑(normSq z) := by
    rw [mul_comm, star_def, mul_conj]
  rw [this, ofReal_re]

/-- The normalized finite trace is nonnegative on a squared modulus. -/
theorem stageTrace_star_mul_self_re_nonneg (n : ℕ) (f : DiagAlg n) :
    0 ≤ (stageTrace n (diagMul n (diagStar n f) f)).re := by
  dsimp [stageTrace, diagMul, diagStar]
  have h_sum_nonneg : 0 ≤ ∑ w : BitWord n, normSq (f w) := by
    apply Finset.sum_nonneg
    intro w hw
    exact normSq_nonneg (f w)
  have h_factor : 0 ≤ 1 / (2 ^ n : ℝ) := by positivity
  have h_c_div : (2 ^ n : ℂ)⁻¹ = ↑(1 / (2 ^ n : ℝ)) := by push_cast; simp
  rw [h_c_div]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  have h_sum_re : (∑ w : BitWord n, (starRingEnd ℂ) (f w) * f w).re =
                  ∑ w : BitWord n, normSq (f w) := by
    rw [Complex.re_sum]
    congr 1 with w
    exact star_mul_self_re_eq_normSq (f w)
  rw [h_sum_re]
  exact mul_nonneg h_factor h_sum_nonneg

/-- 🏆 THEOREM 2: Star Involution Commutes with the Inductive Colimit Embedding. -/
theorem diagEmbedSucc_star_comm (n : ℕ) (f : DiagAlg n) :
    diagEmbedSucc n (diagStar n f) = diagStar (n + 1) (diagEmbedSucc n f) := by
  funext w
  dsimp [diagEmbedSucc, diagStar]

/-- 🏆 THEOREM 3: Multiplication Commutes with the Inductive Colimit Embedding. -/
theorem diagEmbedSucc_mul_comm (n : ℕ) (f g : DiagAlg n) :
    diagEmbedSucc n (diagMul n f g) =
      diagMul (n + 1) (diagEmbedSucc n f) (diagEmbedSucc n g) := by
  funext w
  dsimp [diagEmbedSucc, diagMul]

/-- 🏆 THEOREM 4: Weil Positivity Compatibility across the Inductive Colimit. -/
theorem stageTrace_star_compat (n : ℕ) (f : DiagAlg n) :
    stageTrace (n + 1) (diagMul (n + 1) (diagStar (n + 1) (diagEmbedSucc n f)) (diagEmbedSucc n f)) =
      stageTrace n (diagMul n (diagStar n f) f) := by
  rw [← diagEmbedSucc_star_comm]
  rw [← diagEmbedSucc_mul_comm]
  exact stageTrace_diagEmbedSucc n (diagMul n (diagStar n f) f)

/-- Phase multiplier on the complex circle: z * star z = 1. -/
structure PhaseFactor (n : ℕ) where
  u : BitWord n → ℂ
  u_unitary : ∀ w, star (u w) * u w = 1

/-- Pointwise multiplication by the supplied unit-modulus function. -/
def modularPhaseFlow (n : ℕ) (U : PhaseFactor n) (f : DiagAlg n) : DiagAlg n :=
  fun w => U.u w * f w

/-- A unit-modulus multiplier preserves the pointwise squared modulus. -/
theorem modularPhaseFlow_unitary (n : ℕ) (U : PhaseFactor n) (f : DiagAlg n) :
    diagMul n (diagStar n (modularPhaseFlow n U f)) (modularPhaseFlow n U f) =
      diagMul n (diagStar n f) f := by
  funext w
  dsimp [diagMul, diagStar, modularPhaseFlow]
  have h_u := U.u_unitary w
  change (star (U.u w * f w) * (U.u w * f w)) = star (f w) * f w
  have : (star (U.u w * f w) * (U.u w * f w)) = star (f w) * (star (U.u w) * U.u w) * f w := by
    rw [star_mul]
    ring
  rw [this, h_u]
  ring

/-- A unit-modulus multiplier preserves the normalized trace of a squared modulus. -/
theorem stageTrace_modularPhaseFlow_invariant (n : ℕ) (U : PhaseFactor n) (f : DiagAlg n) :
    stageTrace n (diagMul n (diagStar n (modularPhaseFlow n U f)) (modularPhaseFlow n U f)) =
      stageTrace n (diagMul n (diagStar n f) f) := by
  rw [modularPhaseFlow_unitary]

/-- 🏆 THEOREM 7: Master UHF Weil Positivity and Unitarity Synthesis Packet. -/
theorem master_uhf_weil_positivity_synthesis (n : ℕ) (U : PhaseFactor n) (f : DiagAlg n) :
    (0 ≤ (stageTrace n (diagMul n (diagStar n f) f)).re) ∧
    (stageTrace (n + 1) (diagMul (n + 1) (diagStar (n + 1) (diagEmbedSucc n f)) (diagEmbedSucc n f)) =
       stageTrace n (diagMul n (diagStar n f) f)) ∧
    (stageTrace n (diagMul n (diagStar n (modularPhaseFlow n U f)) (modularPhaseFlow n U f)) =
       stageTrace n (diagMul n (diagStar n f) f)) := by
  exact ⟨stageTrace_star_mul_self_re_nonneg n f,
         stageTrace_star_compat n f,
         stageTrace_modularPhaseFlow_invariant n U f⟩

end InfoGeometry.Canonical.UHFWeilPositivity

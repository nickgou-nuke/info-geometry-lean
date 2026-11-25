/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Gromov Tropical Softmax Sandwich, Penrose–Plücker Bilinear XOR, and Born–Fisher Sphere Pullback

Complements `InfoGeometry.LLM.EarlyLearningFoundations` by formalizing the three synthesis
identities connecting 1943–1969 threshold/perceptron models to continuous information geometry
(Source 3 Chunk 170 and Barbaresco TINN Slide 217):
1. **Penrose–Plücker Bilinear XOR**: while single-layer affine perceptrons fail on XOR, the
   squared 2×2 symplectic spinor determinant `⟨λ(x₁), λ(x₂)⟩_ε² = (x₂ - x₁)²` computes Boolean
   XOR exactly around threshold `1 / 2`.
2. **Finite-Temperature Tropical Sandwich**: the scaled log-partition Massieu potential
   `Ψ_β(a) = (1 / β) log ∑ exp(β a_j)` satisfies `a_{j*} ≤ Ψ_β(a) ≤ a_{j*} + (log N) / β`,
   interpolating between smooth Softmax optimization (`β < ∞`) and discrete threshold max (`β → ∞`).
3. **Gromov's Archimedes–Born–Fisher Sphere Theorem (Slide 217)**: under the quadratic Born map
   `p_i = x_i²`, `dp_i = 2 x_i dx_i`, the Fisher quadratic form pulls back to `4 ∑ dx_i²`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.GromovTropicalPluckerFisherBridge

/-! ### Part 1: Penrose–Plücker Bilinear Spinor XOR Resolution -/

/-- Projective spinor lift `λ(x) = (1, x) ∈ ℝ²` of a scalar input `x ∈ ℝ`. -/
def spinorLift (x : ℝ) : Fin 2 → ℝ := ![1, x]

/-- Penrose symplectic spinor bracket (`2 × 2` Plücker minor) `⟨a, b⟩_ε = a₀ b₁ - a₁ b₀`. -/
def spinorBracket (a b : Fin 2 → ℝ) : ℝ :=
  a 0 * b 1 - a 1 * b 0

/-- Squared bilinear Plücker–Attention XOR score `⟨λ(x₁), λ(x₂)⟩_ε²`. -/
def pluckerXOR (x₁ x₂ : ℝ) : ℝ :=
  (spinorBracket (spinorLift x₁) (spinorLift x₂)) ^ 2

/-- Explicit formula `pluckerXOR x₁ x₂ = (x₂ - x₁)²`. -/
theorem pluckerXOR_eq_sq_sub (x₁ x₂ : ℝ) : pluckerXOR x₁ x₂ = (x₂ - x₁) ^ 2 := by
  simp [pluckerXOR, spinorBracket, spinorLift]

/-- **Bilinear Spinor Resolution of Boolean XOR**:
around decision threshold `1 / 2`, the squared Plücker determinant computes `xor x₁ x₂` exactly. -/
theorem pluckerXOR_computes_bool_xor (x₁ x₂ : Bool) :
    (1 / 2 : ℝ) < pluckerXOR (if x₁ then 1 else 0) (if x₂ then 1 else 0) ↔ xor x₁ x₂ = true := by
  cases x₁ <;> cases x₂ <;> norm_num [pluckerXOR, spinorBracket, spinorLift]

/-! ### Part 2: Finite-Temperature Souriau Massieu Tropical Sandwich (`β → ∞` Limit) -/

/-- Temperature-scaled Souriau log-partition / Softmax potential
`Ψ_β(a) = (1 / β) * log (∑ j, exp (β * a j))`. -/
def tempLogPartition {N : ℕ} (β : ℝ) (a : Fin N → ℝ) : ℝ :=
  (1 / β) * Real.log (∑ j : Fin N, Real.exp (β * a j))

/-- Lower tropical bound: for `β > 0` and every `j₀ : Fin N`, `a j₀ ≤ Ψ_β(a)`. -/
theorem tempLogPartition_lower_bound {N : ℕ} (β : ℝ) (hβ : 0 < β) (a : Fin N → ℝ)
    (j₀ : Fin N) :
    a j₀ ≤ tempLogPartition β a := by
  unfold tempLogPartition
  have hexp_pos : 0 < Real.exp (β * a j₀) := Real.exp_pos _
  have hle_sum : Real.exp (β * a j₀) ≤ ∑ j : Fin N, Real.exp (β * a j) :=
    Finset.single_le_sum (fun j _ => (Real.exp_pos (β * a j)).le) (Finset.mem_univ j₀)
  have hlog : Real.log (Real.exp (β * a j₀)) ≤ Real.log (∑ j : Fin N, Real.exp (β * a j)) :=
    Real.log_le_log hexp_pos hle_sum
  rw [Real.log_exp] at hlog
  have hmul : (1 / β) * (β * a j₀) ≤ (1 / β) * Real.log (∑ j : Fin N, Real.exp (β * a j)) :=
    mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr hβ.le)
  have hcancel : (1 / β) * (β * a j₀) = a j₀ := by
    field_simp [hβ.ne']
  rwa [hcancel] at hmul

/-- Upper tropical bound: if `N > 0`, `β > 0`, and `∀ j, a j ≤ M`,
then `Ψ_β(a) ≤ M + (log N) / β`. -/
theorem tempLogPartition_upper_bound {N : ℕ} (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (a : Fin N → ℝ) (M : ℝ) (hM : ∀ j : Fin N, a j ≤ M) :
    tempLogPartition β a ≤ M + Real.log (N : ℝ) / β := by
  unfold tempLogPartition
  have hterm : ∀ j : Fin N, Real.exp (β * a j) ≤ Real.exp (β * M) := fun j =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hM j) hβ.le)
  have hsum_le : (∑ j : Fin N, Real.exp (β * a j)) ≤ (N : ℝ) * Real.exp (β * M) := by
    calc
      ∑ j : Fin N, Real.exp (β * a j) ≤ ∑ _j : Fin N, Real.exp (β * M) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = (N : ℝ) * Real.exp (β * M) := by simp
  have hsum_pos : 0 < ∑ j : Fin N, Real.exp (β * a j) := by
    let j0 : Fin N := ⟨0, hN⟩
    exact Finset.sum_pos (fun j _ => Real.exp_pos (β * a j)) ⟨j0, Finset.mem_univ j0⟩
  have hlog : Real.log (∑ j : Fin N, Real.exp (β * a j)) ≤
      Real.log ((N : ℝ) * Real.exp (β * M)) :=
    Real.log_le_log hsum_pos hsum_le
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [Real.log_mul hNpos.ne' (Real.exp_pos (β * M)).ne', Real.log_exp] at hlog
  have hmul : (1 / β) * Real.log (∑ j : Fin N, Real.exp (β * a j)) ≤
      (1 / β) * (Real.log (N : ℝ) + β * M) :=
    mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr hβ.le)
  have hrhs : (1 / β) * (Real.log (N : ℝ) + β * M) = M + Real.log (N : ℝ) / β := by
    field_simp [hβ.ne']
    ring
  rwa [hrhs] at hmul

/-- **Finite-Temperature Tropical Sandwich**:
Around any maximum logit `j*`, `a j* ≤ Ψ_β(a) ≤ a j* + (log N) / β`. -/
theorem tempLogPartition_tropical_sandwich {N : ℕ} (hN : 0 < N) (β : ℝ) (hβ : 0 < β)
    (a : Fin N → ℝ) (jStar : Fin N) (hjStar : ∀ j : Fin N, a j ≤ a jStar) :
    a jStar ≤ tempLogPartition β a ∧ tempLogPartition β a ≤ a jStar + Real.log (N : ℝ) / β :=
  ⟨tempLogPartition_lower_bound β hβ a jStar,
   tempLogPartition_upper_bound hN β hβ a (a jStar) hjStar⟩

/-! ### Part 3: Gromov's Archimedes–Born–Fisher Round-Sphere Pullback (Barbaresco Slide 217) -/

/-- Quadratic Born-rule map `p_i = x_i²` from ℝ^N to `ℝ_{≥0}^N`. -/
def bornMap {N : ℕ} (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => x i ^ 2

/-- Fisher–Rao quadratic form `∑_i v_i² / p_i` on positive coordinates. -/
def fisherQuadraticForm {N : ℕ} (p v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, v i ^ 2 / p i

/-- **Gromov's Archimedes–Born–Fisher Sphere Theorem**:
For any nowhere-vanishing vector `x : Fin N → ℝ` and tangent perturbation `v : Fin N → ℝ`,
pulling back the Fisher metric along `p_i = x_i²` (`dp_i = 2 x_i v_i`) gives `4 ∑_i v_i²`. -/
theorem gromov_born_fisher_sphere_pullback {N : ℕ} (x v : Fin N → ℝ)
    (hx : ∀ i : Fin N, x i ≠ 0) :
    fisherQuadraticForm (bornMap x) (fun i => 2 * x i * v i) = 4 * ∑ i : Fin N, v i ^ 2 := by
  unfold fisherQuadraticForm bornMap
  have hterm : ∀ i : Fin N, (2 * x i * v i) ^ 2 / x i ^ 2 = 4 * v i ^ 2 := fun i => by
    have hxi : x i ≠ 0 := hx i
    field_simp [hxi]
    ring
  simp_rw [hterm, ← Finset.mul_sum]

end InfoGeometry.Canonical.GromovTropicalPluckerFisherBridge

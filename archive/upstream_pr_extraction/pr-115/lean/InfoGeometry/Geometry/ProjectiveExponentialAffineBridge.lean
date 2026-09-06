/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Projective-Exponential Affine Bridge

This module formalizes the exact mathematical bridge between projective geometry
and exponential/information geometry through the homogeneous positive cone:

$$\mathcal{C}^\times = \{ x \in \mathbb{R}^{n+1} \mid \forall i, x_i > 0 \}$$

1. **Projective Ray Quotient**:
   $$\mathbb{P}(\mathbb{R}^{n+1}_{>0}) = \mathcal{C}^\times / \mathbb{R}_{>0}^\times$$
   under positive scaling $x \sim c \cdot x$ ($c > 0$).

2. **Affine Section / Normalization**:
   The probability simplex section $\text{normalize}(x) = \frac{x}{\sum_i x_i}$ with $\sum_i p_i = 1$.

3. **Logarithmic / Exponential Duality**:
   The logarithm $\theta_i = \log x_i$ converts multiplicative scaling into additive translations:
   $$x \mapsto c \cdot x \iff \theta \mapsto \theta + (\log c) \mathbf{1}$$

4. **Isomorphism of Quotients**:
   $$\mathbb{P}(\mathbb{R}^{n+1}_{>0}) \cong \mathbb{R}^{n+1} / \mathbb{R}\mathbf{1}$$

5. **Softmax / Gibbs Invariance**:
   The softmax parameterization $\text{softmax}(\theta)_i = \frac{e^{\theta_i}}{\sum_j e^{\theta_j}}$
   is gauge-invariant under shifts $\theta \mapsto \theta + c \mathbf{1}$.
-/

open BigOperators

noncomputable section

namespace InfoGeometry.Geometry.ProjectiveExponentialAffineBridge

/-- The positive homogeneous cone in `ℝⁿ⁺¹`. -/
def PosCone (n : ℕ) : Type :=
  { x : Fin (n + 1) → ℝ // ∀ i, 0 < x i }

/-- Sum of coordinates of a positive cone vector is strictly positive. -/
theorem posCone_sum_pos {n : ℕ} (x : PosCone n) :
    0 < ∑ i : Fin (n + 1), x.1 i := by
  apply Finset.sum_pos
  · intro i _
    exact x.2 i
  · exact Finset.univ_nonempty

theorem posCone_sum_ne_zero {n : ℕ} (x : PosCone n) :
    (∑ i : Fin (n + 1), x.1 i) ≠ 0 :=
  ne_of_gt (posCone_sum_pos x)

/-- Equivalence relation on the positive cone by positive scaling rays. -/
def posRaySetoid (n : ℕ) : Setoid (PosCone n) where
  r x y := ∃ c : ℝ, 0 < c ∧ y.1 = c • x.1
  iseqv := {
    refl := fun x => ⟨1, Real.zero_lt_one, by simp⟩
    symm := fun {x y} ⟨c, hc, h⟩ => ⟨c⁻¹, inv_pos.mpr hc, by
      rw [h, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]⟩
    trans := fun {x y z} ⟨c1, hc1, h1⟩ ⟨c2, hc2, h2⟩ => ⟨c2 * c1, mul_pos hc2 hc1, by
      rw [h2, h1, smul_smul]⟩
  }

/-- The projective positive ray space `ℙ(ℝⁿ⁺¹_{>0})`. -/
def PosProjectiveRay (n : ℕ) : Type :=
  Quotient (posRaySetoid n)

/-- Simplex normalization of a positive cone vector. -/
def simplexNormalize {n : ℕ} (x : PosCone n) : Fin (n + 1) → ℝ :=
  (∑ i, x.1 i)⁻¹ • x.1

/-- Normalized simplex coordinates sum to 1. -/
@[simp] theorem simplexNormalize_sum {n : ℕ} (x : PosCone n) :
    ∑ i, simplexNormalize x i = 1 := by
  dsimp [simplexNormalize]
  rw [← Finset.mul_sum]
  exact inv_mul_cancel₀ (posCone_sum_ne_zero x)

/-- Normalized coordinates are strictly positive. -/
theorem simplexNormalize_pos {n : ℕ} (x : PosCone n) (i : Fin (n + 1)) :
    0 < simplexNormalize x i := by
  dsimp [simplexNormalize]
  exact mul_pos (inv_pos.mpr (posCone_sum_pos x)) (x.2 i)

/-- 🏆 THEOREM: Simplex normalization is scaling-invariant:
    `normalize(c • x) = normalize(x)` for all `c > 0`. -/
theorem simplexNormalize_scale_invariant {n : ℕ} (x : PosCone n) (c : ℝ) (hc : 0 < c) :
    simplexNormalize ⟨c • x.1, fun i => mul_pos hc (x.2 i)⟩ = simplexNormalize x := by
  dsimp [simplexNormalize]
  ext i
  dsimp
  rw [← Finset.mul_sum]
  rw [mul_inv_rev]
  calc
    (∑ i, x.1 i)⁻¹ * c⁻¹ * (c * x.1 i) = (c⁻¹ * c) * ((∑ i, x.1 i)⁻¹ * x.1 i) := by ring
    _ = 1 * ((∑ i, x.1 i)⁻¹ * x.1 i) := by rw [inv_mul_cancel₀ (ne_of_gt hc)]
    _ = (∑ i, x.1 i)⁻¹ * x.1 i := by ring

/-- Logarithmic coordinate map from the positive cone to `ℝⁿ⁺¹`. -/
def logMap {n : ℕ} (x : PosCone n) : Fin (n + 1) → ℝ :=
  fun i => Real.log (x.1 i)

/-- Exponential coordinate map from `ℝⁿ⁺¹` to the positive cone. -/
def expMap {n : ℕ} (θ : Fin (n + 1) → ℝ) : PosCone n :=
  ⟨fun i => Real.exp (θ i), fun i => Real.exp_pos (θ i)⟩

/-- Equivalence relation on `ℝⁿ⁺¹` modulo constant additive translations (gauge shifts `θ ↦ θ + c 1`). -/
def shiftSetoid (n : ℕ) : Setoid (Fin (n + 1) → ℝ) where
  r θ1 θ2 := ∃ c : ℝ, θ2 = θ1 + fun _ : Fin (n + 1) => c
  iseqv := {
    refl := fun θ => ⟨0, by ext i; simp⟩
    symm := fun {θ1 θ2} ⟨c, h⟩ => ⟨-c, by
      ext i
      have hi := congrFun h i
      dsimp at hi ⊢
      linarith⟩
    trans := fun {θ1 θ2 θ3} ⟨c1, h1⟩ ⟨c2, h2⟩ => ⟨c1 + c2, by
      ext i
      have h1i := congrFun h1 i
      have h2i := congrFun h2 i
      dsimp at h1i h2i ⊢
      linarith⟩
  }

/-- The quotient space of log-affine coordinates `ℝⁿ⁺¹ / ℝ 1`. -/
def LogAffineClass (n : ℕ) : Type :=
  Quotient (shiftSetoid n)

/-- 🏆 THEOREM: Logarithm transforms multiplicative scaling into additive translation:
    `log (c • x) = log x + (log c) 1`. -/
theorem logMap_smul {n : ℕ} (x : PosCone n) (c : ℝ) (hc : 0 < c) :
    logMap ⟨c • x.1, fun i => mul_pos hc (x.2 i)⟩ =
      logMap x + fun _ : Fin (n + 1) => Real.log c := by
  ext i
  dsimp [logMap]
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (x.2 i))]
  ring

/-- 🏆 THEOREM: Exponential transforms additive translation into multiplicative scaling:
    `exp (θ + c 1) = eᶜ • exp θ`. -/
theorem expMap_add_const {n : ℕ} (θ : Fin (n + 1) → ℝ) (c : ℝ) :
    (expMap (θ + fun _ : Fin (n + 1) => c)).1 = Real.exp c • (expMap θ).1 := by
  ext i
  dsimp [expMap]
  rw [Real.exp_add]
  ring

/-- Canonical quotient map from positive projective rays to log-affine shift classes. -/
def toLogAffineClass {n : ℕ} : PosProjectiveRay n → LogAffineClass n :=
  Quotient.lift
    (fun x => Quotient.mk (shiftSetoid n) (logMap x))
    (by
      rintro x y ⟨c, hc, h⟩
      apply Quotient.sound
      dsimp
      refine ⟨Real.log c, ?_⟩
      ext i
      have hi := congrFun h i
      dsimp [logMap] at hi ⊢
      rw [hi, Real.log_mul (ne_of_gt hc) (ne_of_gt (x.2 i))]
      ring)

/-- Canonical quotient map from log-affine shift classes to positive projective rays. -/
def toPosProjectiveRay {n : ℕ} : LogAffineClass n → PosProjectiveRay n :=
  Quotient.lift
    (fun θ => Quotient.mk (posRaySetoid n) (expMap θ))
    (by
      rintro θ1 θ2 ⟨c, h⟩
      apply Quotient.sound
      dsimp
      refine ⟨Real.exp c, Real.exp_pos c, ?_⟩
      ext i
      have hi := congrFun h i
      dsimp [expMap] at hi ⊢
      rw [hi, Real.exp_add]
      ring)

/-- 🏆 MASTER THEOREM (Projective-Exponential Isomorphism):
    The positive projective ray quotient `ℙ(ℝⁿ⁺¹_{>0})` is naturally isomorphic
    to the affine log-quotient `ℝⁿ⁺¹ / ℝ 1`. -/
def projectiveExponentialEquiv (n : ℕ) :
    PosProjectiveRay n ≃ LogAffineClass n where
  toFun := toLogAffineClass
  invFun := toPosProjectiveRay
  left_inv := by
    intro q
    induction q using Quotient.ind
    rename_i x
    apply Quotient.sound
    dsimp [toPosProjectiveRay, toLogAffineClass]
    refine ⟨1, Real.zero_lt_one, ?_⟩
    ext i
    dsimp [expMap, logMap]
    rw [Real.exp_log (x.2 i), one_mul]
  right_inv := by
    intro q
    induction q using Quotient.ind
    rename_i θ
    apply Quotient.sound
    dsimp [toPosProjectiveRay, toLogAffineClass]
    refine ⟨0, ?_⟩
    ext i
    dsimp [expMap, logMap]
    rw [Real.log_exp, add_zero]

/-- Softmax / Gibbs parameterization on `ℝⁿ⁺¹`. -/
def softmax {n : ℕ} (θ : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  simplexNormalize (expMap θ)

/-- 🏆 THEOREM: Softmax is shift-invariant: `softmax (θ + c 1) = softmax θ`. -/
theorem softmax_shift_invariant {n : ℕ} (θ : Fin (n + 1) → ℝ) (c : ℝ) :
    softmax (θ + fun _ : Fin (n + 1) => c) = softmax θ := by
  dsimp [softmax, simplexNormalize]
  have hexp : (expMap (θ + fun _ : Fin (n + 1) => c)).1 = Real.exp c • (expMap θ).1 :=
    expMap_add_const θ c
  ext i
  dsimp [simplexNormalize]
  rw [hexp]
  dsimp
  rw [← Finset.mul_sum]
  have hpos : 0 < Real.exp c := Real.exp_pos c
  have hne : Real.exp c ≠ 0 := ne_of_gt hpos
  rw [mul_inv_rev]
  calc
    (∑ i, (expMap θ).1 i)⁻¹ * (Real.exp c)⁻¹ * (Real.exp c * (expMap θ).1 i) =
      ((Real.exp c)⁻¹ * Real.exp c) * ((∑ i, (expMap θ).1 i)⁻¹ * (expMap θ).1 i) := by ring
    _ = 1 * ((∑ i, (expMap θ).1 i)⁻¹ * (expMap θ).1 i) := by rw [inv_mul_cancel₀ hne]
    _ = (∑ i, (expMap θ).1 i)⁻¹ * (expMap θ).1 i := by ring

end InfoGeometry.Geometry.ProjectiveExponentialAffineBridge

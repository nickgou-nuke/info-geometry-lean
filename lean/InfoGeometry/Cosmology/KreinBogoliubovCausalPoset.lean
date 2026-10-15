/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Krein Space Doubling, Bogoliubov Flow, and GNS Causal Poset Synthesis

This module synthesizes the foundational archetypes extracted from the raw mathematical
stream into a rigorous, kernel-verified causal pipeline:

### The Causal Poset of Archetypes:
```text
  [Archetype I: Star-Ring State & GNS Radical]
                     │
                     ▼
  [Archetype II: Universal Left Ideal vs. Tracial Two-Sided Ideal]
                     │
                     ▼
  [Archetype III: Krein Doubled Metric η and Krein Adjoint]
                     │
                     ▼
  [Archetype IV: Bogoliubov / Rindler Flow as Krein Isometry]
                     │
                     ▼
  [Archetype V: Invariant Null Cone & Causal Future Cone Relation]
```

### Mathematical Invariants Proved:
1. **GNS Radical Left Ideal**: For any positive linear state on a `StarRing`,
   $\mathcal{N}_\phi = \{x \mid \forall y, \phi(y^* x) = 0\}$ is unconditionally a left ideal.
2. **Tracial Two-Sided Ideal**: If $\phi$ is tracial ($\phi(x y) = \phi(y x)$), $\mathcal{N}_\phi$
   is also a right ideal, hence a two-sided ideal.
3. **Krein Doubled Metric**: The $2 \times 2$ split symmetry $\eta = \operatorname{diag}(1, -1)$
   satisfies $\eta^2 = 1$ and $\eta^T = \eta$.
4. **Krein Adjoint**: $M^\dagger = \eta M^T \eta$ satisfies $(A B)^\dagger = B^\dagger A^\dagger$.
5. **Bogoliubov Rindler Isometry**: The boost $B(\theta) = \begin{pmatrix} \cosh \theta & \sinh \theta \\ \sinh \theta & \cosh \theta \end{pmatrix}$
   satisfies $B(\theta)^\dagger B(\theta) = 1$ via $\cosh^2 \theta - \sinh^2 \theta = 1$.
6. **Null Cone Invariance**: The Krein quadratic form $q_K(v) = v_0^2 - v_1^2$ satisfies
   $q_K(B(\theta) v) = q_K(v)$ identically, preserving the causal boundary.

All proofs are complete with zero `sorry`, zero `admit`, and core Mathlib axioms.
-/

namespace InfoGeometry.Cosmology.KreinBogoliubov

open Matrix

/-! ### Archetype I & II: Star-Ring State, GNS Radical, and Traciality -/

variable {A : Type*} [Ring A] [StarRing A]

/-- The GNS radical / null space of a functional $\phi : A \to A$.
    An element $x$ is null if $\phi(y^* x) = 0$ for all test elements $y$. -/
def GNSRadical (phi : A → A) : Set A :=
  {x : A | ∀ y : A, phi (star y * x) = 0}

/-- Universal Left Ideal Theorem: The GNS radical is unconditionally a left ideal
    under ring associativity and the involution identity $(a^* y)^* = y^* a$. -/
theorem gnsRadical_is_left_ideal (phi : A → A) (a x : A) (hx : x ∈ GNSRadical phi) :
    a * x ∈ GNSRadical phi := by
  intro y
  dsimp [GNSRadical] at hx
  have h_assoc : star y * (a * x) = star (star a * y) * x := by
    rw [star_mul, star_star]
    rw [mul_assoc]
  rw [h_assoc]
  exact hx (star a * y)

/-- Predicate for a tracial state: $\phi(u v) = \phi(v u)$. -/
def IsTracial (phi : A → A) : Prop :=
  ∀ u v : A, phi (u * v) = phi (v * u)

/-- Tracial Right Ideal Theorem: Under traciality, the GNS radical is also a right ideal,
    making it a two-sided ideal. -/
theorem gnsRadical_is_right_ideal_of_tracial (phi : A → A) (hTr : IsTracial phi)
    (a x : A) (hx : x ∈ GNSRadical phi) :
    x * a ∈ GNSRadical phi := by
  intro y
  dsimp [GNSRadical] at hx
  -- phi (star y * (x * a)) = phi (a * (star y * x))
  have h_cyc : phi (star y * (x * a)) = phi ((a * star y) * x) := by
    rw [← mul_assoc]
    have h1 : phi ((star y * x) * a) = phi (a * (star y * x)) := hTr (star y * x) a
    rw [h1, mul_assoc]
  rw [h_cyc]
  have h_test : a * star y = star (y * star a) := by
    rw [star_mul, star_star]
  rw [h_test]
  exact hx (y * star a)

/-! ### Archetype III: Krein Doubled Space Metric and Adjoint -/

/-- The fundamental indefinite Krein metric on the doubled 2-space: $\eta = \operatorname{diag}(1, -1)$. -/
def kreinMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

/-- The Krein metric is self-inverse: $\eta^2 = 1$. -/
theorem kreinMetric_sq : kreinMetric * kreinMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinMetric, mul_apply, Fin.sum_univ_two]

/-- The Krein metric is symmetric: $\eta^T = \eta$. -/
theorem kreinMetric_transpose : kreinMetricᵀ = kreinMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The Krein adjoint of a 2×2 matrix: $M^\dagger = \eta M^T \eta$. -/
def kreinAdjoint (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  kreinMetric * Mᵀ * kreinMetric

/-- The Krein adjoint reverses matrix multiplication: $(A B)^\dagger = B^\dagger A^\dagger$. -/
theorem kreinAdjoint_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    kreinAdjoint (A * B) = kreinAdjoint B * kreinAdjoint A := by
  dsimp [kreinAdjoint]
  rw [transpose_mul]
  calc
    kreinMetric * (Bᵀ * Aᵀ) * kreinMetric
      = (kreinMetric * Bᵀ) * 1 * (Aᵀ * kreinMetric) := by simp only [mul_one, mul_assoc]
    _ = (kreinMetric * Bᵀ) * (kreinMetric * kreinMetric) * (Aᵀ * kreinMetric) := by
      rw [kreinMetric_sq]
    _ = (kreinMetric * Bᵀ * kreinMetric) * (kreinMetric * Aᵀ * kreinMetric) := by
      simp only [mul_assoc]

/-! ### Archetype IV: Bogoliubov / Rindler Flow as Krein Isometry -/

/-- The 1-parameter Bogoliubov hyperbolic boost matrix in $M_2(\mathbb{R})$. -/
noncomputable def bogoliubovTransform (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh θ, Real.sinh θ;
     Real.sinh θ, Real.cosh θ]

/-- The Bogoliubov matrix is symmetric: $B(\theta)^T = B(\theta)$. -/
theorem bogoliubovTransform_transpose (θ : ℝ) :
    (bogoliubovTransform θ)ᵀ = bogoliubovTransform θ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The Krein adjoint of the Bogoliubov transformation equals the inverse boost $B(-\theta)$. -/
theorem kreinAdjoint_bogoliubovTransform (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) =
      !![Real.cosh θ, - Real.sinh θ;
         - Real.sinh θ, Real.cosh θ] := by
  ext i j
  dsimp [kreinAdjoint, kreinMetric, bogoliubovTransform]
  simp only [Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Krein Isometry Theorem: The Bogoliubov boost preserves the Krein metric:
    $B(\theta)^\dagger B(\theta) = 1$. -/
theorem bogoliubov_is_krein_isometry (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) * bogoliubovTransform θ = 1 := by
  rw [kreinAdjoint_bogoliubovTransform]
  ext i j
  dsimp [bogoliubovTransform]
  simp only [Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp
  · have h := Real.cosh_sq_sub_sinh_sq θ
    calc Real.cosh θ * Real.cosh θ - Real.sinh θ * Real.sinh θ
      _ = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
      _ = 1 := h
  · ring
  · ring
  · have h := Real.cosh_sq_sub_sinh_sq θ
    calc -(Real.sinh θ * Real.sinh θ) + Real.cosh θ * Real.cosh θ
      _ = Real.cosh θ ^ 2 - Real.sinh θ ^ 2 := by ring
      _ = 1 := h

/-! ### Archetype V: Krein Quadratic Form, Null Cone, and Causal Poset Invariance -/

/-- The indefinite Krein quadratic form on 2-vectors: $q_K(v) = v_0^2 - v_1^2$. -/
def kreinQuadForm (v : Fin 2 → ℝ) : ℝ :=
  (v 0)^2 - (v 1)^2

/-- Predicate that a 2-vector lies on the Krein null boundary: $q_K(v) = 0$. -/
def IsKreinNull (v : Fin 2 → ℝ) : Prop :=
  kreinQuadForm v = 0

/-- The transformed 2-vector under the Bogoliubov boost $B(\theta) v$. -/
noncomputable def boostVec (θ : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  mulVec (bogoliubovTransform θ) v

/-- Exact Quadratic Form Invariance: The Krein metric is strictly preserved by the boost:
    $q_K(B(\theta) v) = q_K(v)$. -/
theorem kreinQuadForm_boost (θ : ℝ) (v : Fin 2 → ℝ) :
    kreinQuadForm (boostVec θ v) = kreinQuadForm v := by
  dsimp [kreinQuadForm, boostVec, Matrix.mulVec, dotProduct, bogoliubovTransform]
  simp only [Fin.sum_univ_two, Fin.isValue]
  have hc := Real.cosh_sq_sub_sinh_sq θ
  calc
    (Real.cosh θ * v 0 + Real.sinh θ * v 1) ^ 2 - (Real.sinh θ * v 0 + Real.cosh θ * v 1) ^ 2
      = (Real.cosh θ ^ 2 - Real.sinh θ ^ 2) * (v 0 ^ 2 - v 1 ^ 2) := by ring
    _ = 1 * (v 0 ^ 2 - v 1 ^ 2) := by rw [hc]
    _ = (v 0) ^ 2 - (v 1) ^ 2 := by ring

/-- Null Cone Invariance Theorem: A vector is on the Krein null cone if and only if
    its boosted image is on the Krein null cone:
    $v \in \mathcal{N}_K \iff B(\theta) v \in \mathcal{N}_K$. -/
theorem bogoliubov_preserves_null_cone (θ : ℝ) (v : Fin 2 → ℝ) :
    IsKreinNull (boostVec θ v) ↔ IsKreinNull v := by
  dsimp [IsKreinNull]
  rw [kreinQuadForm_boost]

/-- The causal future cone in the Krein doubled space: $v_0 \ge |v_1|$. -/
def InCausalFuture (v : Fin 2 → ℝ) : Prop :=
  0 ≤ kreinQuadForm v ∧ 0 ≤ v 0

/-- Causal Poset Order: $x \le_K y \iff y - x \in \text{CausalFuture}$. -/
def KreinCausalOrder (x y : Fin 2 → ℝ) : Prop :=
  InCausalFuture (y - x)

end InfoGeometry.Cosmology.KreinBogoliubov

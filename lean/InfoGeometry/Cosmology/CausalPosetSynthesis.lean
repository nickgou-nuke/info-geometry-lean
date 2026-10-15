/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Causal Poset Synthesis: 2×2 Algebraic Spinor Model

This module formalizes a concrete 2×2 matrix algebraic model capturing five foundational 
causal archetypes bridging indefinite Krein metric spaces, hyperbolic Lorentz boosts, 
twistor dyadic incidence, GNS vacuum radicals, and pure state projector curvature bounds.

## The Causal Poset (𝒫₀ ⟶ 𝒫₄)

* **𝒫₀: Indefinite Krein Space** 
  Split Krein adjoint $M^\dagger = \eta M^T \eta$ and Bogoliubov isometry $B^\dagger B = \mathbf{1}$.
* **𝒫₁: Null Cone Conservation & Hyperbolic Boost Flow**
  Exact null cone conservation $q_K(B v) = q_K(v)$ under the 1-parameter hyperbolic boost subgroup.
* **𝒫₂: Twistor Dyadic Incidence**
  Penrose twistor incidence $v \cdot u = 0 \iff D^2 = 0$.
* **𝒫₃: The 2×2 GNS Radical & Parabolic Coset Identification**
  GNS annihilator $A \in \mathcal{N}_\omega \iff A|\Omega\rangle = 0$. 
  Vacuum stabilizer $\operatorname{Stab}_{\mathrm{SL}(2,\mathbb{R})}(|\Omega\rangle) = P$.
* **𝒫₄: Parabolic Coset Singularity Resolution**
  Universal bounded expectations $|\omega(\Pi)| \le 1$, global normalization $\|\Pi\|_F^2 = 1$, 
  and universally bounded commutator curvature $\|[K, \Pi]\|_F^2 \le 1/2$.
-/

namespace InfoGeometry.CausalPoset

open Matrix
open scoped Matrix

/-! ### 𝒫₀: Indefinite Krein Space & Adjoints -/

/-- The fundamental indefinite (1, -1) Krein metric. -/
def kreinMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- The Krein metric is self-inverse. -/
theorem kreinMetric_sq : kreinMetric * kreinMetric = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kreinMetric, mul_apply, Fin.sum_univ_two]

/-- The Krein adjoint of an operator: $M^\dagger = \eta M^T \eta$. -/
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

/-! ### 𝒫₁: Null Cone Conservation & Hyperbolic Boost Flow -/

/-- The 1-parameter Bogoliubov hyperbolic boost matrix in $M_2(\mathbb{R})$. -/
noncomputable def bogoliubovTransform (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh θ, Real.sinh θ; Real.sinh θ, Real.cosh θ]

/-- The Bogoliubov matrix is symmetric. -/
theorem bogoliubovTransform_transpose (θ : ℝ) :
    (bogoliubovTransform θ)ᵀ = bogoliubovTransform θ := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The Krein adjoint of the Bogoliubov transformation equals the inverse boost. -/
theorem kreinAdjoint_bogoliubovTransform (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) =
      !![Real.cosh θ, - Real.sinh θ;
         - Real.sinh θ, Real.cosh θ] := by
  ext i j
  dsimp [kreinAdjoint, kreinMetric, bogoliubovTransform]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Krein Isometry Theorem: The Bogoliubov boost preserves the Krein metric $B(\theta)^\dagger B(\theta) = 1$. -/
theorem bogoliubov_is_krein_isometry (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) * bogoliubovTransform θ = 1 := by
  rw [kreinAdjoint_bogoliubovTransform]
  ext i j
  dsimp [bogoliubovTransform]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.one_apply]
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

/-- The indefinite Krein quadratic form $q_K(v) = v_0^2 - v_1^2$. -/
def kreinQuadForm (v : Fin 2 → ℝ) : ℝ :=
  (v 0)^2 - (v 1)^2

/-- Exact Null Cone Conservation: The Krein quadratic form is strictly preserved. -/
theorem kreinQuadForm_boost (θ : ℝ) (v : Fin 2 → ℝ) :
    kreinQuadForm (mulVec (bogoliubovTransform θ) v) = kreinQuadForm v := by
  dsimp [kreinQuadForm, mulVec, dotProduct, bogoliubovTransform]
  simp only [Fin.sum_univ_two, Fin.isValue]
  have hc := Real.cosh_sq_sub_sinh_sq θ
  calc
    (Real.cosh θ * v 0 + Real.sinh θ * v 1)^2 - (Real.sinh θ * v 0 + Real.cosh θ * v 1)^2
      = ((Real.cosh θ)^2 - (Real.sinh θ)^2) * (v 0)^2 - ((Real.cosh θ)^2 - (Real.sinh θ)^2) * (v 1)^2 := by ring
    _ = 1 * (v 0)^2 - 1 * (v 1)^2 := by rw [hc]
    _ = (v 0)^2 - (v 1)^2 := by ring

/-! ### 𝒫₂: Twistor Dyadic Incidence & Operator Nilpotency -/

/-- The dyadic transition operator (outer product) $D(u, v) = u v^T$. -/
def dyadicMatrix (u v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  of (fun i j => u i * v j)

/-- Dyadic squaring identity: $D(u, v)^2 = (v \cdot u) D(u, v)$. -/
theorem dyadicMatrix_sq (u v : Fin 2 → ℝ) :
    dyadicMatrix u v * dyadicMatrix u v = (v 0 * u 0 + v 1 * u 1) • dyadicMatrix u v := by
  ext i j
  simp only [dyadicMatrix, mul_apply, of_apply, Fin.sum_univ_two, Fin.isValue, Matrix.smul_apply]
  calc
    u i * v 0 * (u 0 * v j) + u i * v 1 * (u 1 * v j)
      = (v 0 * u 0 + v 1 * u 1) * (u i * v j) := by ring
    _ = (v 0 * u 0 + v 1 * u 1) • (u i * v j) := by rfl

/-- Twistor Incidence Theorem: The operator is nilpotent iff the twistors are incident. -/
theorem dyadicMatrix_nilpotent_iff (u v : Fin 2 → ℝ) :
    dyadicMatrix u v * dyadicMatrix u v = 0 ↔ (v 0 * u 0 + v 1 * u 1) = 0 := by
  constructor
  · intro h
    have tr_h : (dyadicMatrix u v * dyadicMatrix u v) 0 0 + (dyadicMatrix u v * dyadicMatrix u v) 1 1 = 0 := by
      rw [h]
      simp
    simp only [dyadicMatrix, mul_apply, of_apply, Fin.sum_univ_two, Fin.isValue] at tr_h
    have alg : (v 0 * u 0 + v 1 * u 1)^2 = 0 := by
      calc (v 0 * u 0 + v 1 * u 1)^2 
        _ = u 0 * v 0 * (u 0 * v 0) + u 0 * v 1 * (u 1 * v 0) + (u 1 * v 0 * (u 0 * v 1) + u 1 * v 1 * (u 1 * v 1)) := by ring
        _ = 0 := tr_h
    exact sq_eq_zero_iff.mp alg
  · intro h
    rw [dyadicMatrix_sq]
    rw [h, zero_smul]

/-! ### 𝒫₃: The 2×2 GNS Radical & Parabolic Coset Identification -/

/-- The cyclic vacuum state vector |Ω⟩. -/
def cyclicVacuum : Fin 2 → ℝ := ![1, 0]

/-- The evaluation functional corresponding to the cyclic vacuum state. -/
def vacuumState (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := 
  A 0 0

/-- The Gelfand Null Radical: { A | ∀ B, ω(Bᵀ A) = 0 }. -/
def InGNSNull (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ B : Matrix (Fin 2) (Fin 2) ℝ, vacuumState (Bᵀ * A) = 0

/-- GNS Annihilator Theorem: A ∈ 𝒩_ω ⟺ A|Ω⟩ = 0. -/
theorem inGNSNull_iff_mulVec_vacuum (A : Matrix (Fin 2) (Fin 2) ℝ) :
    InGNSNull A ↔ mulVec A cyclicVacuum = 0 := by
  constructor
  · intro h
    have h0 : A 0 0 = 0 := by
      have h1 := h !![1, 0; 0, 0]
      simp [vacuumState, mul_apply, transpose_apply, Fin.sum_univ_two] at h1
      linarith
    have h1 : A 1 0 = 0 := by
      have h2 := h !![0, 0; 1, 0]
      simp [vacuumState, mul_apply, transpose_apply, Fin.sum_univ_two] at h2
      linarith
    ext i
    fin_cases i <;> simp [mulVec, cyclicVacuum, dotProduct, Fin.sum_univ_two, Fin.isValue, h0, h1]
  · intro h B
    have ha0 : A 0 0 = 0 := by 
      have h' := congr_fun h 0
      simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two] at h'
      exact h'
    have ha1 : A 1 0 = 0 := by 
      have h' := congr_fun h 1
      simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two] at h'
      exact h'
    simp [vacuumState, mul_apply, Fin.sum_univ_two, transpose_apply, ha0, ha1]

/-- Predicate for the upper-triangular Parabolic Subgroup P. -/
def IsParabolicUpper (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  g 1 0 = 0

/-- Predicate for SL(2, ℝ). -/
def IsSL2 (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  g.det = 1

/-- A matrix stabilizes the vacuum ray if g|Ω⟩ = λ|Ω⟩ for some λ ≠ 0. -/
def StabilizesVacuumRay (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  IsSL2 g ∧ ∃ lambda_val : ℝ, lambda_val ≠ 0 ∧ mulVec g cyclicVacuum = lambda_val • cyclicVacuum

/-- Parabolic Coset Identification: Stab_{SL(2, ℝ)}(|Ω⟩) = P. -/
theorem stabilizesVacuumRay_iff_parabolic (g : Matrix (Fin 2) (Fin 2) ℝ) :
    StabilizesVacuumRay g ↔ IsSL2 g ∧ IsParabolicUpper g := by
  constructor
  · rintro ⟨hSL2, lambda_val, _, h_ray⟩
    refine ⟨hSL2, ?_⟩
    dsimp [IsParabolicUpper]
    have h1 := congr_fun h_ray 1
    simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two] at h1
    exact h1
  · rintro ⟨hSL2, hP⟩
    refine ⟨hSL2, g 0 0, ?_, ?_⟩
    · intro hz
      dsimp [IsSL2] at hSL2
      rw [det_fin_two] at hSL2
      dsimp [IsParabolicUpper] at hP
      rw [hz, hP] at hSL2
      linarith
    · ext i
      fin_cases i
      · simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two]
      · simp [mulVec, dotProduct, cyclicVacuum, Fin.sum_univ_two]
        exact hP

/-! ### 𝒫₄: Parabolic Coset Singularity Resolution -/

/-- The quantum state density projector Π(u) = u uᵀ. -/
def projector (u : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u 0 * u 0, u 0 * u 1;
     u 1 * u 0, u 1 * u 1]

/-- The squared Frobenius norm of a 2x2 matrix. -/
def frobNormSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A 0 0)^2 + (A 0 1)^2 + (A 1 0)^2 + (A 1 1)^2

/-- Universal Bounded Expectation: |ω(Π(u))| ≤ 1. -/
theorem vacuumState_projector_bound (u : Fin 2 → ℝ) (hu : (u 0)^2 + (u 1)^2 = 1) :
    |vacuumState (projector u)| ≤ 1 := by
  dsimp [vacuumState, projector]
  have h_abs : |u 0 * u 0| = (u 0)^2 := by rw [← sq, abs_of_nonneg (sq_nonneg _)]
  rw [h_abs]
  have h_u1_sq : 0 ≤ (u 1)^2 := sq_nonneg (u 1)
  linarith

/-- Global State Normalization: ‖Π‖_F² = 1 universally. -/
theorem projector_frobNormSq (u : Fin 2 → ℝ) (hu : (u 0)^2 + (u 1)^2 = 1) :
    frobNormSq (projector u) = 1 := by
  dsimp [frobNormSq, projector]
  calc
    (u 0 * u 0)^2 + (u 0 * u 1)^2 + (u 1 * u 0)^2 + (u 1 * u 1)^2
      = (u 0)^4 + 2 * (u 0)^2 * (u 1)^2 + (u 1)^4 := by ring
    _ = ((u 0)^2 + (u 1)^2)^2 := by ring
    _ = 1^2 := by rw [hu]
    _ = 1 := by ring

/-- The Lorentz boost generator K. -/
noncomputable def boostGenerator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1/2 : ℝ), 0; 0, -(1/2 : ℝ)]

/-- Matrix commutator [A, B] = A B - B A. -/
def commutator (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A * B - B * A

/-- Explicit calculation of the boost-projector commutator. -/
theorem boost_projector_commutator (u : Fin 2 → ℝ) :
    commutator boostGenerator (projector u) = !![0, u 0 * u 1; - (u 0 * u 1), 0] := by
  ext i j
  dsimp [commutator, boostGenerator, projector]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
  fin_cases i <;> fin_cases j <;> (simp; try ring)

/-- Bounded Commutator Curvature: ‖[K, Π(u)]‖_F² ≤ 1/2 for all unit pure state projectors. -/
theorem commutator_boost_projector_bound (u : Fin 2 → ℝ) (hu : (u 0)^2 + (u 1)^2 = 1) :
    frobNormSq (commutator boostGenerator (projector u)) ≤ 1 / 2 := by
  rw [boost_projector_commutator]
  dsimp [frobNormSq]
  have h_amgm : ((u 0)^2 - (u 1)^2)^2 ≥ 0 := sq_nonneg _
  have h_exp : ((u 0)^2 - (u 1)^2)^2 = ((u 0)^2 + (u 1)^2)^2 - 4 * (u 0 * u 1)^2 := by ring
  rw [hu] at h_exp
  linarith

end InfoGeometry.CausalPoset

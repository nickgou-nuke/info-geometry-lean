/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import InfoGeometry.Modular.ConnesCocycle

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Super-KMS Condition on Graded CAR Algebras with Chiral Derivation ad_{β·Γ}

Formalizes the $\mathbb{Z}_2hBcgraded Kubo–Martin–Schwinger (Super-KMS) condition
on a graded *-algebra under the chiral modular generator induced by the grading involution `Γ`:

  1. `gradedSign`: Koszul parity sign factor `(-1)^{|a||b|}` for `|a|, |b| ∈ ℤ₂`.
  2. `SuperKMS1BoundaryCondition`: Analytic strip boundary conditions:
       - Real line:       `F_{a,b}(t)     = ω(a * σ_t(b))`
       - Shifted line:    `F_{a,b}(t + i) = (-1)^{|a||b|} ω(σ_t(b) * a)`
  3. `IsSuperKMS1State`: Normalized functional satisfying the graded KMS condition.
  4. `IsAlgebraicSuperKMS1`: Finite-dimensional / entire state formulation:
       `ω(a * b) = (-1)^{|a||b|} ω(b * σ_i(a))`
  5. `LinearDerivation`: Leibniz derivation on non-commutative algebras.
  6. `infinitesimal_super_kms_skew_adjoint`: Infinitesimal graded skew-symmetry:
       `ω(a * δ(b)) = -(-1)^{|a||b|} ω(δ(a) * b)`.

All proofs are complete in native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Modular.SuperKMS

open Complex
open InfoGeometry.Modular.ConnesCocycle

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-! =========================================================================
    1. ℤ₂-Grading and Koszul Sign Factor
    ========================================================================= -/

/-- Parity degree in ℤ₂ = {0, 1}. -/
abbrev Parity := ZMod 2

/-- Koszul sign factor `(-1)^{deg(a) * deg(b)} ∈ ℂ`. -/
def gradedSign (p q : Parity) : ℂ :=
  if p = 1 ∧ q = 1 then -1 else 1

@[simp]
theorem gradedSign_even_left (q : Parity) : gradedSign 0 q = 1 := by
  dsimp [gradedSign]

@[simp]
theorem gradedSign_even_right (p : Parity) : gradedSign p 0 = 1 := by
  dsimp [gradedSign]
  split_ifs with h
  · have h0 : (0 : ZMod 2) = 1 := h.2
    revert h0
    decide
  · rfl

@[simp]
theorem gradedSign_odd_odd : gradedSign 1 1 = -1 := by
  dsimp [gradedSign]

theorem gradedSign_symm (p q : Parity) : gradedSign p q = gradedSign q p := by
  dsimp [gradedSign]
  by_cases h : p = 1 ∧ q = 1
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have h_rev : ¬ (q = 1 ∧ p = 1) := by intro ⟨hq, hp⟩; exact h ⟨hp, hq⟩
    simp [h, h_rev]

theorem gradedSign_sq (p q : Parity) : gradedSign p q * gradedSign p q = 1 := by
  dsimp [gradedSign]
  split_ifs <;> ring

/-- Single-element parity sign `(-1)^p ∈ {1, -1} ⊂ ℂ`. -/
def paritySign (p : Parity) : ℂ :=
  if p = 1 then -1 else 1

@[simp]
theorem paritySign_zero : paritySign 0 = 1 := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp [paritySign, h01]

@[simp]
theorem paritySign_one : paritySign 1 = -1 := by
  simp [paritySign]

private theorem parity_cases (p : Parity) : p = 0 ∨ p = 1 := by
  fin_cases p
  · left; rfl
  · right; rfl

@[simp]
theorem paritySign_sq (p : Parity) : paritySign p * paritySign p = 1 := by
  rcases parity_cases p with rfl | rfl <;> simp

theorem paritySign_mul (p q : Parity) :
    paritySign p * paritySign q = paritySign (p + q) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases parity_cases p with rfl | rfl <;> rcases parity_cases q with rfl | rfl <;> simp [h11]

theorem paritySign_mul_eq_gradedSign (p q : Parity) :
    paritySign (p * q) = gradedSign p q := by
  rcases parity_cases p with rfl | rfl <;> rcases parity_cases q with rfl | rfl <;> simp

/-- Homogeneity of `a : A` with parity `p : ZMod 2` relative to grading element `Gamma`:
`Gamma * a = (-1)^p • (a * Gamma)`. -/
def IsHomogeneous (Gamma : A) (p : Parity) (a : A) : Prop :=
  Gamma * a = paritySign p • (a * Gamma)

theorem isHomogeneous_one (Gamma : A) : IsHomogeneous Gamma 0 (1 : A) := by
  simp [IsHomogeneous]

theorem isHomogeneous_add {Gamma : A} {p : Parity} {a b : A}
    (ha : IsHomogeneous Gamma p a) (hb : IsHomogeneous Gamma p b) :
    IsHomogeneous Gamma p (a + b) := by
  unfold IsHomogeneous at ha hb ⊢
  rw [mul_add, ha, hb, add_mul, smul_add]

theorem isHomogeneous_neg {Gamma : A} {p : Parity} {a : A}
    (ha : IsHomogeneous Gamma p a) :
    IsHomogeneous Gamma p (-a) := by
  unfold IsHomogeneous at ha ⊢
  rw [mul_neg, ha, neg_mul, smul_neg]

theorem isHomogeneous_smul {Gamma : A} {p : Parity} (c : ℂ) {a : A}
    (ha : IsHomogeneous Gamma p a) :
    IsHomogeneous Gamma p (c • a) := by
  unfold IsHomogeneous at ha ⊢
  rw [mul_smul_comm, ha, smul_mul_assoc, smul_comm c (paritySign p)]

theorem isHomogeneous_mul {Gamma : A} {p q : Parity} {a b : A}
    (ha : IsHomogeneous Gamma p a) (hb : IsHomogeneous Gamma q b) :
    IsHomogeneous Gamma (p + q) (a * b) := by
  unfold IsHomogeneous at ha hb ⊢
  calc
    Gamma * (a * b) = (Gamma * a) * b := (mul_assoc _ _ _).symm
    _ = (paritySign p • (a * Gamma)) * b := by rw [ha]
    _ = paritySign p • (a * (Gamma * b)) := by rw [smul_mul_assoc, mul_assoc]
    _ = paritySign p • (a * (paritySign q • (b * Gamma))) := by rw [hb]
    _ = (paritySign p * paritySign q) • ((a * b) * Gamma) := by
        rw [mul_smul_comm, smul_smul, mul_assoc]
    _ = paritySign (p + q) • ((a * b) * Gamma) := by rw [paritySign_mul]

/-! =========================================================================
    2. Modular Automorphism Flow
    ========================================================================= -/

/-- 1-parameter modular automorphism group `σ_t`. -/
abbrev ModularFlow (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] :=
  InfoGeometry.Modular.ConnesCocycle.ModularFlow ℂ A

/-! =========================================================================
    3. Super-KMS Boundary Condition at β = 1
    ========================================================================= -/

/--
Super-KMS boundary condition on the strip `{0 ≤ Im(z) ≤ 1}` for homogeneous elements:
  - Real line:       `F_{a,b}(t)     = ω(a * σ t b)`
  - Shifted line:    `F_{a,b}(t + i) = (-1)^{|a||b|} ω(σ t b * a)`
-/
structure SuperKMS1BoundaryCondition
    (ω : A →ₗ[ℂ] ℂ) (σ : ModularFlow A) (deg : A → Parity) (a b : A) (F : ℂ → ℂ) : Prop where
  boundary_real : ∀ (t : ℝ), F (t : ℂ) = ω (a * σ t b)
  boundary_shift : ∀ (t : ℝ), F ((t : ℂ) + Complex.I) = (gradedSign (deg a) (deg b)) * ω (σ t b * a)

/--
A linear functional `ω : A → ℂ` is a **Super-KMS-1 State** with grading `deg` if:
  1. It is normalized: `ω(1) = 1`
  2. For every pair of homogeneous elements `a, b`, there exists an analytic
     correlation function `F_{a,b}` satisfying the graded boundary relations.
-/
structure IsSuperKMS1State (ω : A →ₗ[ℂ] ℂ) (σ : ModularFlow A) (deg : A → Parity) : Prop where
  normalized : ω 1 = 1
  has_correlation : ∀ (a b : A), ∃ (F : ℂ → ℂ), SuperKMS1BoundaryCondition ω σ deg a b F

/-! =========================================================================
    4. Algebraic Super-KMS Form (Gibbs Supertrace)
    ========================================================================= -/

/--
Algebraic Super-KMS relation at `t = 0`:
  `ω(a * b) = (-1)^{|a||b|} ω(b * σ_i(a))`
-/
def IsAlgebraicSuperKMS1 (ω : A →ₗ[ℂ] ℂ) (σ_i : A →ₐ[ℂ] A) (deg : A → Parity) : Prop :=
  ∀ (a b : A), ω (a * b) = (gradedSign (deg a) (deg b)) * ω (b * σ_i a)

/--
Algebraic Super-KMS-1 condition restricted to homogeneous pairs `(p, a)` and `(q, b)`
relative to grading element `Gamma`:
  `ω(a * b) = (-1)^{p q} ω(b * σ_i(a))`
-/
def IsAlgebraicSuperKMS1Homogeneous (ω : A →ₗ[ℂ] ℂ) (σ_i : A →ₐ[ℂ] A) (Gamma : A) : Prop :=
  ∀ (p q : Parity) (a b : A),
    IsHomogeneous Gamma p a → IsHomogeneous Gamma q b →
      ω (a * b) = (gradedSign p q) * ω (b * σ_i a)

/-- Canonical supertrace functional `STr_ρ(x) = Tr(Γ * ρ * x)`. -/
def supertraceState (tr : A →ₗ[ℂ] ℂ) (Gamma rho : A) : A →ₗ[ℂ] ℂ where
  toFun x := tr (Gamma * rho * x)
  map_add' x y := by
    simp only [mul_add, map_add]
  map_smul' c x := by
    simp only [mul_smul_comm, map_smul, RingHom.id_apply]

@[simp]
theorem supertraceState_apply (tr : A →ₗ[ℂ] ℂ) (Gamma rho x : A) :
    supertraceState tr Gamma rho x = tr (Gamma * rho * x) :=
  rfl

/--
Constructive ring-general Algebraic Super-KMS-1 theorem on homogeneous elements:
from trace cyclicity `tr(x * y) = tr(y * x)`, `rho_inv * rho = 1`, `Gamma * rho = rho * Gamma`,
and `σ_i a = rho * a * rho_inv` (with NO circular `h_cycl_perm` assumption).
-/
theorem supertrace_is_algebraic_super_kms_homogeneous
    (tr : A →ₗ[ℂ] ℂ)
    (h_cycl : ∀ (x y : A), tr (x * y) = tr (y * x))
    (Gamma rho rho_inv : A)
    (h_inv : rho_inv * rho = 1)
    (h_rho_comm : Gamma * rho = rho * Gamma)
    (sigma_i : A →ₐ[ℂ] A)
    (h_sigma_i : ∀ a, sigma_i a = rho * a * rho_inv) :
    IsAlgebraicSuperKMS1Homogeneous (supertraceState tr Gamma rho) sigma_i Gamma := by
  intro p q a b ha hb
  dsimp [supertraceState]
  rw [h_sigma_i a]
  have h_step :
      tr (Gamma * rho * (b * (rho * a * rho_inv))) =
        paritySign q * tr (Gamma * rho * (a * b)) := by
    calc
      tr (Gamma * rho * (b * (rho * a * rho_inv)))
          = tr ((Gamma * rho * b * rho * a) * rho_inv) := by
              congr 1; simp only [mul_assoc]
      _ = tr (rho_inv * (Gamma * rho * b * rho * a)) := h_cycl _ _
      _ = tr ((rho_inv * (Gamma * rho)) * (b * rho * a)) := by
              congr 1; simp only [mul_assoc]
      _ = tr ((rho_inv * (rho * Gamma)) * (b * rho * a)) := by
              rw [h_rho_comm]
      _ = tr (((rho_inv * rho) * Gamma) * (b * rho * a)) := by
              congr 1; simp only [mul_assoc]
      _ = tr ((Gamma * b) * (rho * a)) := by
              rw [h_inv, one_mul]; congr 1; simp only [mul_assoc]
      _ = tr ((paritySign q • (b * Gamma)) * (rho * a)) := by
              rw [hb]
      _ = paritySign q * tr (b * (Gamma * rho * a)) := by
              rw [smul_mul_assoc, map_smul, smul_eq_mul]
              congr 2; simp only [mul_assoc]
      _ = paritySign q * tr ((Gamma * rho * a) * b) := by
              rw [h_cycl b (Gamma * rho * a)]
      _ = paritySign q * tr (Gamma * rho * (a * b)) := by
              congr 2; simp only [mul_assoc]
  rcases parity_cases p with rfl | rfl <;> rcases parity_cases q with rfl | rfl
  · rw [h_step]
    simp
  · have ha0 : Gamma * a = a * Gamma := by
      simpa [IsHomogeneous] using ha
    have hb1 : Gamma * b = -(b * Gamma) := by
      simpa [IsHomogeneous] using hb
    have h_neg_self : tr (Gamma * rho * (a * b)) = -tr (Gamma * rho * (a * b)) := by
      calc
        tr (Gamma * rho * (a * b))
            = tr ((Gamma * rho * a) * b) := by congr 1; simp only [mul_assoc]
        _ = tr (b * (Gamma * rho * a)) := h_cycl _ _
        _ = tr (b * ((rho * Gamma) * a)) := by
            congr 1; congr 1; rw [h_rho_comm]
        _ = tr (b * (rho * (Gamma * a))) := by
            congr 1; simp only [mul_assoc]
        _ = tr (b * (rho * (a * Gamma))) := by
            rw [ha0]
        _ = tr ((b * rho * a) * Gamma) := by
            congr 1; simp only [mul_assoc]
        _ = tr (Gamma * (b * rho * a)) := h_cycl _ _
        _ = tr ((Gamma * b) * (rho * a)) := by
            congr 1; simp only [mul_assoc]
        _ = tr ((-(b * Gamma)) * (rho * a)) := by
            rw [hb1]
        _ = -tr (b * (Gamma * rho * a)) := by
            rw [neg_mul, map_neg]; congr 2; simp only [mul_assoc]
        _ = -tr ((Gamma * rho * a) * b) := by
            rw [h_cycl b (Gamma * rho * a)]
        _ = -tr (Gamma * rho * (a * b)) := by
            congr 2; simp only [mul_assoc]
    have h_zero : tr (Gamma * rho * (a * b)) = 0 := by
      have h2 : (2 : ℂ) * tr (Gamma * rho * (a * b)) = 0 := by
        calc
          (2 : ℂ) * tr (Gamma * rho * (a * b))
              = tr (Gamma * rho * (a * b)) + tr (Gamma * rho * (a * b)) := two_mul _
          _ = tr (Gamma * rho * (a * b)) + (-tr (Gamma * rho * (a * b))) := by
              conv_lhs => rhs; rw [h_neg_self]
          _ = 0 := add_neg_cancel _
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    rw [h_step, h_zero]
    simp
  · rw [h_step]
    simp
  · rw [h_step]
    simp

/--
THEOREM: If every element is homogeneous under `deg` relative to `Gamma`, then the
supertrace functional `ω(x) = STr(ρ * x) = Tr(Γ * ρ * x)` satisfies `IsAlgebraicSuperKMS1`
directly from trace cyclicity (no circular `h_cycl_perm`).
-/
theorem supertrace_is_algebraic_super_kms
    (tr : A →ₗ[ℂ] ℂ)
    (h_cycl : ∀ (x y : A), tr (x * y) = tr (y * x))
    (Gamma rho rho_inv : A)
    (h_inv : rho_inv * rho = 1)
    (h_rho_comm : Gamma * rho = rho * Gamma)
    (deg : A → Parity)
    (h_hom : ∀ a, IsHomogeneous Gamma (deg a) a)
    (sigma_i : A →ₐ[ℂ] A)
    (h_sigma_i : ∀ a, sigma_i a = rho * a * rho_inv) :
    IsAlgebraicSuperKMS1 (supertraceState tr Gamma rho) sigma_i deg := by
  intro a b
  exact supertrace_is_algebraic_super_kms_homogeneous
    tr h_cycl Gamma rho rho_inv h_inv h_rho_comm sigma_i h_sigma_i
    (deg a) (deg b) a b (h_hom a) (h_hom b)

/-! =========================================================================
    4b. Constructive Graded Matrix Algebra Realization & Inhomogeneous Obstruction
    ========================================================================= -/

section MatrixSuperKMS

open Matrix

/-- Block-diagonal grading involution `Γ = diag(I_{ι₀}, -I_{ι₁})` on `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ`. -/
def superGradingMatrix (ι₀ ι₁ : Type*) [Fintype ι₀] [DecidableEq ι₀]
    [Fintype ι₁] [DecidableEq ι₁] : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Even block-diagonal projection `(M₁₁, 0; 0, M₂₂)`. -/
def matrixEvenPart {ι₀ ι₁ : Type*} (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ :=
  Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂

/-- Odd block-off-diagonal projection `(0, M₁₂; M₂₁, 0)`. -/
def matrixOddPart {ι₀ ι₁ : Type*} (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ :=
  Matrix.fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0

theorem matrix_even_odd_decomp {ι₀ ι₁ : Type*} (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    M = matrixEvenPart M + matrixOddPart M := by
  ext (i | i) (j | j) <;>
    simp [matrixEvenPart, matrixOddPart, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem matrixEvenPart_isHomogeneous {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    [Fintype ι₁] [DecidableEq ι₁] (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    IsHomogeneous (superGradingMatrix ι₀ ι₁) 0 (matrixEvenPart M) := by
  unfold IsHomogeneous superGradingMatrix matrixEvenPart
  rw [paritySign_zero, one_smul, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem matrixOddPart_isHomogeneous {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    [Fintype ι₁] [DecidableEq ι₁] (M : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    IsHomogeneous (superGradingMatrix ι₀ ι₁) 1 (matrixOddPart M) := by
  unfold IsHomogeneous superGradingMatrix matrixOddPart
  rw [paritySign_one, neg_one_smul, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;> simp

/-- Constructive `IsAlgebraicSuperKMS1Homogeneous` on `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ`
for arbitrary finite `ι₀, ι₁` and any grading-commuting density `ρ` with inverse `ρ_inv`. -/
theorem supertraceState_matrix_is_algebraic_super_kms
    {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
    (ρ ρ_inv : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (h_inv : ρ_inv * ρ = 1)
    (h_rho_comm : superGradingMatrix ι₀ ι₁ * ρ = ρ * superGradingMatrix ι₀ ι₁)
    (σ_i : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ →ₐ[ℂ] Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (h_σ : ∀ a, σ_i a = ρ * a * ρ_inv) :
    IsAlgebraicSuperKMS1Homogeneous
      (supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) (superGradingMatrix ι₀ ι₁) ρ)
      σ_i (superGradingMatrix ι₀ ι₁) := by
  intro p q a b ha hb
  exact supertrace_is_algebraic_super_kms_homogeneous
    (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ)
    (fun x y => Matrix.trace_mul_comm x y)
    (superGradingMatrix ι₀ ι₁) ρ ρ_inv h_inv h_rho_comm σ_i h_σ
    p q a b ha hb

/-- Exact **inhomogeneous Super-KMS obstruction formula** on `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ`:
the failure of trace cyclicity on arbitrary mixed-parity operators `a, b` is exactly twice
the supertrace of the odd–odd product `matrixOddPart a * matrixOddPart b`. -/
theorem supertrace_matrix_inhomogeneous_obstruction
    {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
    (ρ ρ_inv : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (h_inv : ρ_inv * ρ = 1)
    (h_rho_comm : superGradingMatrix ι₀ ι₁ * ρ = ρ * superGradingMatrix ι₀ ι₁)
    (σ_i : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ →ₐ[ℂ] Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (h_σ : ∀ a, σ_i a = ρ * a * ρ_inv)
    (a b : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) (superGradingMatrix ι₀ ι₁) ρ (a * b) -
      supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) (superGradingMatrix ι₀ ι₁) ρ
        (b * σ_i a) =
      2 * supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) (superGradingMatrix ι₀ ι₁) ρ
        (matrixOddPart a * matrixOddPart b) := by
  let ω := supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) (superGradingMatrix ι₀ ι₁) ρ
  have hkms := supertraceState_matrix_is_algebraic_super_kms ρ ρ_inv h_inv h_rho_comm σ_i h_σ
  have ha0 := matrixEvenPart_isHomogeneous a
  have ha1 := matrixOddPart_isHomogeneous a
  have hb0 := matrixEvenPart_isHomogeneous b
  have hb1 := matrixOddPart_isHomogeneous b
  have h00 := hkms 0 0 (matrixEvenPart a) (matrixEvenPart b) ha0 hb0
  have h01 := hkms 0 1 (matrixEvenPart a) (matrixOddPart b) ha0 hb1
  have h10 := hkms 1 0 (matrixOddPart a) (matrixEvenPart b) ha1 hb0
  have h11 := hkms 1 1 (matrixOddPart a) (matrixOddPart b) ha1 hb1
  simp only [gradedSign_even_left, gradedSign_even_right, gradedSign_odd_odd, one_mul,
    neg_one_mul] at h00 h01 h10 h11
  have ha_dec : a = matrixEvenPart a + matrixOddPart a := matrix_even_odd_decomp a
  have hb_dec : b = matrixEvenPart b + matrixOddPart b := matrix_even_odd_decomp b
  have hL :
      ω (a * b) =
        ω (matrixEvenPart a * matrixEvenPart b) + ω (matrixEvenPart a * matrixOddPart b) +
          ω (matrixOddPart a * matrixEvenPart b) + ω (matrixOddPart a * matrixOddPart b) := by
    conv_lhs => rw [ha_dec, hb_dec, add_mul, mul_add, mul_add, map_add, map_add, map_add]
    abel
  have hR :
      ω (b * σ_i a) =
        ω (matrixEvenPart b * σ_i (matrixEvenPart a)) +
          ω (matrixOddPart b * σ_i (matrixEvenPart a)) +
          ω (matrixEvenPart b * σ_i (matrixOddPart a)) +
          ω (matrixOddPart b * σ_i (matrixOddPart a)) := by
    conv_lhs =>
      rw [ha_dec, hb_dec, map_add, add_mul, mul_add, mul_add, map_add, map_add, map_add]
    abel
  rw [hL, hR, h00, h01, h10]
  have h11' : ω (matrixOddPart b * σ_i (matrixOddPart a)) =
      -ω (matrixOddPart a * matrixOddPart b) := by
    rw [h11, neg_neg]
  rw [h11']
  calc
    ω (matrixEvenPart b * σ_i (matrixEvenPart a)) +
        ω (matrixOddPart b * σ_i (matrixEvenPart a)) +
        ω (matrixEvenPart b * σ_i (matrixOddPart a)) +
        ω (matrixOddPart a * matrixOddPart b) -
      (ω (matrixEvenPart b * σ_i (matrixEvenPart a)) +
        ω (matrixOddPart b * σ_i (matrixEvenPart a)) +
        ω (matrixEvenPart b * σ_i (matrixOddPart a)) +
        -ω (matrixOddPart a * matrixOddPart b))
        = ω (matrixOddPart a * matrixOddPart b) + ω (matrixOddPart a * matrixOddPart b) := by abel
    _ = 2 * ω (matrixOddPart a * matrixOddPart b) := (two_mul _).symm

/-- Concrete nonvanishing inhomogeneous Super-KMS obstruction witness on `Fin 1 ⊕ Fin 1`:
for `a = E₀₀ + E₀₁` and `b = E₀₀ + E₁₀` with `ρ = 1`, `STr(a * b) - STr(b * a) = 2 ≠ 0`. -/
theorem supertrace_matrix_inhomogeneous_obstruction_nonzero_witness :
    let a : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := Matrix.fromBlocks 1 1 0 0
    let b : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := Matrix.fromBlocks 1 0 1 0
    let ω := supertraceState (Matrix.traceLinearMap (Fin 1 ⊕ Fin 1) ℂ ℂ)
      (superGradingMatrix (Fin 1) (Fin 1)) 1
    ω (a * b) - ω (b * a) = 2 := by
  intro a b ω
  have h := supertrace_matrix_inhomogeneous_obstruction
    (ι₀ := Fin 1) (ι₁ := Fin 1) 1 1 (mul_one 1) (by rw [mul_one, one_mul])
    (AlgHom.id ℂ _) (fun x => by simp) a b
  simp only [AlgHom.id_apply] at h
  have hodd_a : matrixOddPart a = Matrix.fromBlocks 0 1 0 0 := by
    ext (i | i) (j | j) <;> simp [a, matrixOddPart]
  have hodd_b : matrixOddPart b = Matrix.fromBlocks 0 0 1 0 := by
    ext (i | i) (j | j) <;> simp [b, matrixOddPart]
  change ω (a * b) - ω (b * a) = 2
  rw [h, hodd_a, hodd_b]
  simp [supertraceState, superGradingMatrix, Matrix.fromBlocks_multiply,
    Matrix.traceLinearMap_apply, Matrix.trace, Matrix.diag]

end MatrixSuperKMS

/-! =========================================================================
    5. Chiral & Graded Derivations and Infinitesimal Super-KMS Laws
    ========================================================================= -/

/-- A Leibniz derivation `δ : A → A` over `ℂ`. -/
structure LinearDerivation (R : Type*) (A : Type*) [Ring R] [Ring A] [Module R A] where
  toLinearMap : A →ₗ[R] A
  leibniz' : ∀ (x y : A), toLinearMap (x * y) = toLinearMap x * y + x * toLinearMap y

instance : CoeFun (LinearDerivation ℂ A) (fun _ => A → A) where
  coe D := D.toLinearMap

/-- A `ℤ₂`-graded Leibniz derivation of degree `deg_d : Parity` relative to `Gamma`:
`D(a * b) = D(a) * b + (-1)^{deg_d * p} a * D(b)` for `IsHomogeneous Gamma p a`. -/
structure GradedDerivation (A : Type*) [Ring A] [Algebra ℂ A]
    (Gamma : A) (deg_d : Parity) where
  toLinearMap : A →ₗ[ℂ] A
  graded_leibniz' : ∀ (p : Parity) (x y : A),
    IsHomogeneous Gamma p x →
      toLinearMap (x * y) = toLinearMap x * y + paritySign (deg_d * p) • (x * toLinearMap y)

instance (Gamma : A) (deg_d : Parity) :
    CoeFun (GradedDerivation A Gamma deg_d) (fun _ => A → A) where
  coe D := D.toLinearMap

/-- Every even `LinearDerivation ℂ A` is a `GradedDerivation A Gamma 0`. -/
def LinearDerivation.toGradedDerivation (δ : LinearDerivation ℂ A) (Gamma : A) :
    GradedDerivation A Gamma 0 where
  toLinearMap := δ.toLinearMap
  graded_leibniz' := fun p x y _ => by
    simp only [zero_mul, paritySign_zero, one_smul]
    exact δ.leibniz' x y

/--
Infinitesimal skew-adjointness for an even `LinearDerivation` annihilating `ω`:
`ω(a * δ(b)) = -ω(δ(a) * b)` unconditionally (no `gradedSign = 1` restriction).
-/
theorem infinitesimal_super_kms_skew_adjoint
    (ω : A →ₗ[ℂ] ℂ)
    (δ : LinearDerivation ℂ A)
    (h_inv_deriv : ∀ (x : A), ω (δ x) = 0)
    (a b : A) :
    ω (a * δ b) = -ω (δ a * b) := by
  have h_leibniz : δ (a * b) = δ a * b + a * δ b := δ.leibniz' a b
  have h_zero : ω (δ (a * b)) = 0 := h_inv_deriv (a * b)
  change ω (δ.toLinearMap (a * b)) = 0 at h_zero
  rw [h_leibniz, map_add] at h_zero
  exact eq_neg_of_add_eq_zero_right h_zero

/--
General graded skew-adjointness for any `GradedDerivation` of arbitrary degree `deg_d : Parity`
without any `gradedSign = 1` assumption:
  `ω(a * D(b)) = -(-1)^{deg_d * p} ω(D(a) * b)`.
-/
theorem infinitesimal_super_kms_graded_skew_adjoint
    (ω : A →ₗ[ℂ] ℂ)
    {Gamma : A} {deg_d : Parity}
    (D : GradedDerivation A Gamma deg_d)
    (h_inv_deriv : ∀ (x : A), ω (D x) = 0)
    {p : Parity} {a : A} (ha : IsHomogeneous Gamma p a) (b : A) :
    ω (a * D b) = -(paritySign (deg_d * p)) * ω (D a * b) := by
  have h_leibniz : D (a * b) = D a * b + paritySign (deg_d * p) • (a * D b) :=
    D.graded_leibniz' p a b ha
  have h_zero : ω (D (a * b)) = 0 := h_inv_deriv (a * b)
  change ω (D.toLinearMap (a * b)) = 0 at h_zero
  rw [h_leibniz, map_add, map_smul, smul_eq_mul] at h_zero
  have h1 : paritySign (deg_d * p) * ω (a * D b) = -ω (D a * b) :=
    eq_neg_of_add_eq_zero_right h_zero
  calc
    ω (a * D b) = 1 * ω (a * D b) := (one_mul _).symm
    _ = (paritySign (deg_d * p) * paritySign (deg_d * p)) * ω (a * D b) := by
        rw [paritySign_sq]
    _ = paritySign (deg_d * p) * (paritySign (deg_d * p) * ω (a * D b)) := mul_assoc _ _ _
    _ = paritySign (deg_d * p) * (-ω (D a * b)) := by rw [h1]
    _ = -(paritySign (deg_d * p)) * ω (D a * b) := by ring

/-- Odd `GradedDerivation` (`deg_d = 1`) specialization:
`ω(a * D(b)) = -gradedSign 1 p * ω(D(a) * b)`. -/
theorem infinitesimal_super_kms_odd_skew_adjoint
    (ω : A →ₗ[ℂ] ℂ)
    {Gamma : A}
    (D : GradedDerivation A Gamma 1)
    (h_inv_deriv : ∀ (x : A), ω (D x) = 0)
    {p : Parity} {a : A} (ha : IsHomogeneous Gamma p a) (b : A) :
    ω (a * D b) = -(gradedSign 1 p) * ω (D a * b) := by
  rw [← paritySign_mul_eq_gradedSign 1 p]
  exact infinitesimal_super_kms_graded_skew_adjoint ω D h_inv_deriv ha b

/-- Constructive odd `GradedDerivation A Gamma 1` given by the supercommutator
`x ↦ F * x - (Gamma * x * Gamma) * F` whenever `Gamma * Gamma = 1`. -/
def superInnerDeriv (Gamma F : A) (hGamma : Gamma * Gamma = 1) :
    GradedDerivation A Gamma 1 where
  toLinearMap :=
    { toFun := fun x => F * x - (Gamma * x * Gamma) * F
      map_add' := fun x y => by
        simp only [mul_add, add_mul]
        abel
      map_smul' := fun c x => by
        simp only [mul_smul_comm, smul_mul_assoc, smul_sub, RingHom.id_apply] }
  graded_leibniz' := fun p x y hx => by
    have hGxG : Gamma * x * Gamma = paritySign p • x := by
      calc
        Gamma * x * Gamma = (Gamma * x) * Gamma := rfl
        _ = (paritySign p • (x * Gamma)) * Gamma := by rw [hx]
        _ = paritySign p • (x * (Gamma * Gamma)) := by rw [smul_mul_assoc, mul_assoc]
        _ = paritySign p • x := by rw [hGamma, mul_one]
    have hGxyG : Gamma * (x * y) * Gamma = (Gamma * x * Gamma) * (Gamma * y * Gamma) := by
      calc
        Gamma * (x * y) * Gamma = Gamma * x * 1 * y * Gamma := by simp only [mul_assoc, mul_one]
        _ = Gamma * x * (Gamma * Gamma) * y * Gamma := by rw [hGamma]
        _ = (Gamma * x * Gamma) * (Gamma * y * Gamma) := by simp only [mul_assoc]
    change F * (x * y) - (Gamma * (x * y) * Gamma) * F =
      (F * x - (Gamma * x * Gamma) * F) * y +
        paritySign (1 * p) • (x * (F * y - (Gamma * y * Gamma) * F))
    simp only [hGxyG, one_mul, sub_mul, hGxG, mul_sub, smul_sub, smul_mul_assoc, mul_assoc]
    abel

/-- Every `superInnerDeriv Gamma F` annihilates the supertrace functional `supertraceState tr Gamma 1`
whenever `tr` is cyclic and `Gamma * Gamma = 1`. -/
theorem supertrace_superInnerDeriv_zero
    (tr : A →ₗ[ℂ] ℂ) (h_cycl : ∀ x y : A, tr (x * y) = tr (y * x))
    (Gamma F : A) (hGamma : Gamma * Gamma = 1) (x : A) :
    supertraceState tr Gamma 1 (superInnerDeriv Gamma F hGamma x) = 0 := by
  dsimp [supertraceState, superInnerDeriv]
  rw [mul_one, mul_sub, map_sub]
  have h1 : tr (Gamma * (F * x)) = tr (Gamma * ((Gamma * x * Gamma) * F)) := by
    calc
      tr (Gamma * (F * x)) = tr ((Gamma * F) * x) := by rw [mul_assoc]
      _ = tr (x * (Gamma * F)) := h_cycl _ _
      _ = tr ((1 * x) * (Gamma * F)) := by rw [one_mul]
      _ = tr (((Gamma * Gamma) * x) * (Gamma * F)) := by rw [hGamma]
      _ = tr (Gamma * ((Gamma * x * Gamma) * F)) := by congr 1; simp only [mul_assoc]
  rw [h1, sub_self]

/--
Reversed Super-KMS skew-adjointness for an even `LinearDerivation` under
`IsAlgebraicSuperKMS1Homogeneous`:
  `ω(a * δ(b)) = -(-1)^{p q} ω(b * σ_i(δ(a)))`
for homogeneous `(p, δ a)` and `(q, b)`, with no `gradedSign = 1` assumption.
-/
theorem infinitesimal_super_kms_skew_adjoint_reversed
    (ω : A →ₗ[ℂ] ℂ) (σ_i : A →ₐ[ℂ] A) (Gamma : A)
    (h_kms : IsAlgebraicSuperKMS1Homogeneous ω σ_i Gamma)
    (δ : LinearDerivation ℂ A)
    (h_inv_deriv : ∀ (x : A), ω (δ x) = 0)
    {p q : Parity} {a b : A}
    (hδa : IsHomogeneous Gamma p (δ a))
    (hb : IsHomogeneous Gamma q b) :
    ω (a * δ b) = -(gradedSign p q) * ω (b * σ_i (δ a)) := by
  rw [infinitesimal_super_kms_skew_adjoint ω δ h_inv_deriv a b]
  rw [h_kms p q (δ a) b hδa hb]
  ring

end InfoGeometry.Modular.SuperKMS

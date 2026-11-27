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
import Mathlib.Tactic
import InfoGeometry.Modular.SuperKMS

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Direct Integration of Trifold Decomposition with Super-KMS Chiral Dynamics

Formalizes the exact connection between:
  1. The Trifold Modular Decomposition `K = α·I + β·Γ + K₀` from `TrifoldRadonNikodymBridge`.
  2. The elimination of the central scalar Weyl mode: `ad_{α·I} = 0`.
  3. The derivation splitting theorem: `ad_K = ad_{β·Γ} + ad_{K₀}`.
  4. The Super-KMS infinitesimal skew-symmetry for the chiral generator `ad_{β·Γ}`.
  5. The coupled Trifold KMS energy-current balance theorem on the graded CAR algebra.

All proofs are complete in native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Modular.TrifoldSuperKMS

open Complex
open InfoGeometry.Modular.SuperKMS

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-! =========================================================================
    1. Commutator Bracket and Inner Derivations
    ========================================================================= -/

/-- Commutator bracket `[K, x] = K * x - x * K`. -/
def bracket (K x : A) : A :=
  K * x - x * K

@[simp]
theorem bracket_apply (K x : A) : bracket K x = K * x - x * K :=
  rfl

/-- Leibniz rule for inner commutators: `[K, xy] = [K, x]y + x[K, y]`. -/
theorem bracket_leibniz (K x y : A) :
    bracket K (x * y) = bracket K x * y + x * bracket K y := by
  dsimp [bracket]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- Inner derivation `ad_K = [K, ·]` bundled as a `LinearDerivation ℂ A`. -/
def innerDeriv (K : A) : LinearDerivation ℂ A where
  toLinearMap := {
    toFun := bracket K
    map_add' := by
      intro x y
      dsimp [bracket]
      simp only [mul_add, add_mul]
      abel
    map_smul' := by
      intro r x
      dsimp [bracket]
      simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  }
  leibniz' := bracket_leibniz K

@[simp]
theorem innerDeriv_apply (K x : A) : innerDeriv K x = K * x - x * K :=
  rfl

/-! =========================================================================
    2. Trifold Decomposition Operators and Derivation Splitting
    ========================================================================= -/

/-- Central scalar mode Hamiltonian: `K_α = α • 1`. -/
def scalarHamiltonian (alpha : ℂ) : A :=
  alpha • (1 : A)

/-- Chiral grading Hamiltonian: `K_β = β • Γ`. -/
def chiralHamiltonian (beta : ℂ) (Gamma : A) : A :=
  beta • Gamma

/--
THEOREM 1 (Central Scalar Mode Vanishing):
The inner derivation of the scalar volume mode `α • 1` is identically zero:
  `ad_{α • 1} = 0`
-/
theorem innerDeriv_scalar_zero (alpha : ℂ) (x : A) :
    innerDeriv (scalarHamiltonian alpha) x = 0 := by
  simp only [innerDeriv_apply, scalarHamiltonian]
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_self]

/-- Linearity of `innerDeriv` under addition of generators. -/
theorem innerDeriv_add (K₁ K₂ x : A) :
    innerDeriv (K₁ + K₂) x = innerDeriv K₁ x + innerDeriv K₂ x := by
  simp only [innerDeriv_apply]
  rw [add_mul, mul_add]
  abel

/-- Linearity of `innerDeriv` under scalar multiplication of generators. -/
theorem innerDeriv_smul (c : ℂ) (K x : A) :
    innerDeriv (c • K) x = c • innerDeriv K x := by
  simp only [innerDeriv_apply]
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

/--
MAIN THEOREM 2 (Trifold Modular Derivation Splitting):
For any modular Hamiltonian `K = α·1 + β·Γ + K₀`, the total modular derivation
splits into the chiral Super-KMS generator `ad_{β·Γ}` and the residual shape derivation `ad_{K₀}`:
  `ad_K = ad_{β·Γ} + ad_{K₀}`
-/
theorem trifold_modular_derivation_split
    (alpha beta : ℂ) (Gamma K₀ : A)
    (K : A) (hK : K = scalarHamiltonian alpha + chiralHamiltonian beta Gamma + K₀)
    (x : A) :
    innerDeriv K x = innerDeriv (chiralHamiltonian beta Gamma) x + innerDeriv K₀ x := by
  rw [hK]
  have h_add : innerDeriv (scalarHamiltonian alpha + chiralHamiltonian beta Gamma + K₀) x =
      innerDeriv (scalarHamiltonian alpha + chiralHamiltonian beta Gamma) x + innerDeriv K₀ x :=
    innerDeriv_add (scalarHamiltonian alpha + chiralHamiltonian beta Gamma) K₀ x
  rw [h_add, innerDeriv_add (scalarHamiltonian alpha) (chiralHamiltonian beta Gamma) x,
      innerDeriv_scalar_zero alpha x, zero_add]

/-! =========================================================================
    3. Super-KMS Graded Skew-Symmetry for the Chiral Mode
    ========================================================================= -/

/--
MAIN THEOREM 3 (Infinitesimal Chiral Super-KMS Identity):
Let `ω` be a linear functional annihilated by the chiral derivation `ω(ad_{β·Γ}(x)) = 0`.
Then `ad_{β·Γ}` is skew-adjoint under `ω` unconditionally (without `gradedSign = 1`):
  `ω(a * ad_{β·Γ}(b)) = -ω(ad_{β·Γ}(a) * b)`
-/
theorem chiral_super_kms_skew_symmetry
    (beta : ℂ) (Gamma : A)
    (ω : A →ₗ[ℂ] ℂ)
    (h_inv : ∀ (x : A), ω (innerDeriv (chiralHamiltonian beta Gamma) x) = 0)
    (a b : A) :
    ω (a * innerDeriv (chiralHamiltonian beta Gamma) b) =
      -ω (innerDeriv (chiralHamiltonian beta Gamma) a * b) := by
  have h_leibniz := (innerDeriv (chiralHamiltonian beta Gamma)).leibniz' a b
  have h_zero : ω (innerDeriv (chiralHamiltonian beta Gamma) (a * b)) = 0 := h_inv (a * b)
  rw [h_leibniz, map_add] at h_zero
  exact eq_neg_of_add_eq_zero_right h_zero

/-- The chiral inner derivation `ad_{β·Γ}` preserves `Gamma`-homogeneity of every degree `p`. -/
theorem innerDeriv_chiralHamiltonian_isHomogeneous
    (beta : ℂ) (Gamma : A) {p : Parity} {a : A}
    (ha : IsHomogeneous Gamma p a) :
    IsHomogeneous Gamma p (innerDeriv (chiralHamiltonian beta Gamma) a) := by
  have hL : IsHomogeneous Gamma p (Gamma * a) := by
    unfold IsHomogeneous at ha ⊢
    calc
      Gamma * (Gamma * a) = Gamma * (paritySign p • (a * Gamma)) := by rw [ha]
      _ = paritySign p • ((Gamma * a) * Gamma) := by rw [mul_smul_comm, mul_assoc]
  have hR : IsHomogeneous Gamma p (a * Gamma) := by
    unfold IsHomogeneous at ha ⊢
    calc
      Gamma * (a * Gamma) = (Gamma * a) * Gamma := (mul_assoc _ _ _).symm
      _ = (paritySign p • (a * Gamma)) * Gamma := by rw [ha]
      _ = paritySign p • ((a * Gamma) * Gamma) := smul_mul_assoc _ _ _
  have h_diff : IsHomogeneous Gamma p (Gamma * a - a * Gamma) := by
    rw [sub_eq_add_neg]
    exact isHomogeneous_add hL (isHomogeneous_neg hR)
  have h_eq : innerDeriv (chiralHamiltonian beta Gamma) a = beta • (Gamma * a - a * Gamma) := by
    simp only [innerDeriv_apply, chiralHamiltonian, smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [h_eq]
  exact isHomogeneous_smul beta h_diff

/--
Reversed Super-KMS chiral skew-symmetry under `IsAlgebraicSuperKMS1Homogeneous`:
for homogeneous `(p, a)` and `(q, b)`,
  `ω(a * ad_{β·Γ}(b)) = -(-1)^{p q} ω(b * σ_i(ad_{β·Γ}(a)))`.
-/
theorem chiral_super_kms_skew_symmetry_reversed
    (beta : ℂ) (Gamma : A)
    (ω : A →ₗ[ℂ] ℂ) (σ_i : A →ₐ[ℂ] A)
    (h_kms : IsAlgebraicSuperKMS1Homogeneous ω σ_i Gamma)
    (h_inv : ∀ (x : A), ω (innerDeriv (chiralHamiltonian beta Gamma) x) = 0)
    {p q : Parity} {a b : A}
    (ha : IsHomogeneous Gamma p a) (hb : IsHomogeneous Gamma q b) :
    ω (a * innerDeriv (chiralHamiltonian beta Gamma) b) =
      -(gradedSign p q) * ω (b * σ_i (innerDeriv (chiralHamiltonian beta Gamma) a)) := by
  have hδa := innerDeriv_chiralHamiltonian_isHomogeneous beta Gamma ha
  rw [chiral_super_kms_skew_symmetry beta Gamma ω h_inv a b]
  rw [h_kms p q (innerDeriv (chiralHamiltonian beta Gamma) a) b hδa hb]
  ring

/-! =========================================================================
    4. Coupled Trifold KMS Energy-Current Balance
    ========================================================================= -/

/--
MAIN THEOREM 4 (Coupled Trifold Current Balance):
The total modular correlation `ω(a * ad_K(b))` decomposes into the Super-KMS chiral
current and the residual trace-free correlation:
  `ω(a * ad_K(b)) = ω(a * ad_{β·Γ}(b)) + ω(a * ad_{K₀}(b))`
-/
theorem trifold_energy_current_balance
    (alpha beta : ℂ) (Gamma K₀ : A)
    (K : A) (hK : K = scalarHamiltonian alpha + chiralHamiltonian beta Gamma + K₀)
    (ω : A →ₗ[ℂ] ℂ)
    (a b : A) :
    ω (a * innerDeriv K b) =
      ω (a * innerDeriv (chiralHamiltonian beta Gamma) b) + ω (a * innerDeriv K₀ b) := by
  have h_split := trifold_modular_derivation_split alpha beta Gamma K₀ K hK b
  rw [h_split, mul_add, map_add]

/-! =========================================================================
    5. Concrete Matrix (ι₀ ⊕ ι₁) Realization of Trifold Super-KMS
    ========================================================================= -/

section MatrixTrifoldSuperKMS

open Matrix

/-- Constructive `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ` trifold modular derivation splitting
with `Γ = superGradingMatrix ι₀ ι₁`. -/
theorem matrix_trifold_modular_derivation_split
    {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
    (alpha beta : ℂ)
    (K₀ X : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    innerDeriv (scalarHamiltonian alpha + chiralHamiltonian beta (superGradingMatrix ι₀ ι₁) + K₀) X =
      innerDeriv (chiralHamiltonian beta (superGradingMatrix ι₀ ι₁)) X + innerDeriv K₀ X := by
  rw [trifold_modular_derivation_split alpha beta (superGradingMatrix ι₀ ι₁) K₀ _ rfl X]

/-- Constructive `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ` trifold current balance under the
supertrace state `ω = STr_ρ`. -/
theorem matrix_trifold_energy_current_balance
    {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
    (alpha beta : ℂ)
    (ρ K₀ a b : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    let Γ := superGradingMatrix ι₀ ι₁
    let ω := supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) Γ ρ
    ω (a * innerDeriv (scalarHamiltonian alpha + chiralHamiltonian beta Γ + K₀) b) =
      ω (a * innerDeriv (chiralHamiltonian beta Γ) b) + ω (a * innerDeriv K₀ b) :=
  trifold_energy_current_balance alpha beta (superGradingMatrix ι₀ ι₁) K₀ _ rfl _ a b

/-- On `Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ`, when `ρ` commutes with `Γ = superGradingMatrix ι₀ ι₁`,
the chiral derivation `ad_{β·Γ}` annihilates `ω = STr_ρ` and therefore satisfies exact
reversed Super-KMS skew-symmetry for any homogeneous pair `(p, a), (q, b)`. -/
theorem matrix_trifold_chiral_annihilates_supertrace
    {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
    (beta : ℂ)
    (ρ : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (h_rho_comm : superGradingMatrix ι₀ ι₁ * ρ = ρ * superGradingMatrix ι₀ ι₁)
    (x : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ) :
    supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) (superGradingMatrix ι₀ ι₁) ρ
      (innerDeriv (chiralHamiltonian beta (superGradingMatrix ι₀ ι₁)) x) = 0 := by
  let Γ := superGradingMatrix ι₀ ι₁
  dsimp [supertraceState, innerDeriv, bracket, chiralHamiltonian]
  rw [Matrix.traceLinearMap_apply]
  have h1 : Γ * ρ * ((beta • Γ) * x - x * (beta • Γ)) =
      beta • ((Γ * ρ * Γ) * x - (Γ * ρ * x) * Γ) := by
    simp only [smul_mul_assoc, mul_smul_comm, mul_sub, mul_assoc, ← smul_sub]
  rw [h1, Matrix.trace_smul, Matrix.trace_sub]
  have hcyc : ((Γ * ρ * x) * Γ).trace = (Γ * (Γ * ρ * x)).trace :=
    Matrix.trace_mul_comm _ _
  have hGcomm : Γ * (Γ * ρ * x) = (Γ * ρ * Γ) * x := by
    calc
      Γ * (Γ * ρ * x) = (Γ * (Γ * ρ)) * x := by simp only [mul_assoc]
      _ = (Γ * (ρ * Γ)) * x := by rw [h_rho_comm]
      _ = (Γ * ρ * Γ) * x := by simp only [mul_assoc]
  rw [hcyc, hGcomm, sub_self, smul_zero]

theorem matrix_trifold_chiral_super_kms_skew_symmetry
    {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
    (beta : ℂ)
    (ρ ρ_inv : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (h_inv : ρ_inv * ρ = 1)
    (h_rho_comm : superGradingMatrix ι₀ ι₁ * ρ = ρ * superGradingMatrix ι₀ ι₁)
    (σ_i : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ →ₐ[ℂ] Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ)
    (h_σ : ∀ a, σ_i a = ρ * a * ρ_inv)
    {p q : Parity} {a b : Matrix (ι₀ ⊕ ι₁) (ι₀ ⊕ ι₁) ℂ}
    (ha : IsHomogeneous (superGradingMatrix ι₀ ι₁) p a)
    (hb : IsHomogeneous (superGradingMatrix ι₀ ι₁) q b) :
    let Γ := superGradingMatrix ι₀ ι₁
    let ω := supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) Γ ρ
    ω (a * innerDeriv (chiralHamiltonian beta Γ) b) =
      -(gradedSign p q) * ω (b * σ_i (innerDeriv (chiralHamiltonian beta Γ) a)) :=
  chiral_super_kms_skew_symmetry_reversed beta (superGradingMatrix ι₀ ι₁)
    (supertraceState (Matrix.traceLinearMap (ι₀ ⊕ ι₁) ℂ ℂ) (superGradingMatrix ι₀ ι₁) ρ)
    σ_i
    (supertraceState_matrix_is_algebraic_super_kms ρ ρ_inv h_inv h_rho_comm σ_i h_σ)
    (matrix_trifold_chiral_annihilates_supertrace beta ρ h_rho_comm)
    ha hb

end MatrixTrifoldSuperKMS

end InfoGeometry.Modular.TrifoldSuperKMS

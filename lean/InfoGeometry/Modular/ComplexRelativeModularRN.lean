/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Modular.ComplexMatrixTomitaDuality
import InfoGeometry.Modular.ConnesCocycle
import InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle
import InfoGeometry.Canonical.PedersenTakesakiRNInterface

/-!
# Noncommuting Complex Relative Modular Operator & Connes Radon–Nikodym Cocycle (`TT-F4`)

This module develops the finite-dimensional complex relative Tomita–Takesaki theory and
noncommuting Connes Radon–Nikodym cocycle on `Matrix (Fin n) (Fin n) ℂ` for pairs of
noncommuting positive invertible densities `(ρ_ψ, ρ_φ)`.

## Main Contents
1. **Part 1 — Relative Tomita & Relative Modular Operators**:
   For `F_ψ F_φ : PositiveComplexDensityFactor n`, defines:
   - `relModularOp F_ψ F_φ X = F_ψ.rho * X * F_φ.rhoInv` (`Δ_{ψ,φ}`),
   - `relModularSqrt F_ψ F_φ X = F_ψ.r * X * F_φ.rInv` (`Δ_{ψ,φ}^{1/2}`),
   - `relTomitaOp F_ψ F_φ X = F_φ.rInv * Xᴴ * F_ψ.r` (`S_{ψ,φ}`),
   - `relTomitaAdjOp F_ψ F_φ X = F_ψ.r * Xᴴ * F_φ.rInv` (`S_{ψ,φ}^*`),
   and proves `S_{ψ,φ}(A r_φ) = Aᴴ r_ψ`, `S_{ψ,φ} = J ∘ Δ_{ψ,φ}^{1/2}` (`relTomitaOp_polar`),
   `S_{ψ,φ}^* ∘ S_{ψ,φ} = Δ_{ψ,φ}`, `J Δ_{ψ,φ} J = Δ_{φ,ψ}^{-1}`, the exact sesquilinearly
   consistent quadratic identity
   `hsInner n (relTomitaOp F_ψ F_φ X) (relTomitaOp F_ψ F_φ Y) =`
   `hsInner n Y (relModularOp F_ψ F_φ X)`,
   Hilbert–Schmidt positivity/faithfulness of `Δ_{ψ,φ}`, and the two-state KMS identity
   `state F_φ (A * relModularOp F_ψ F_φ B) = state F_ψ (B * A)`.

2. **Part 2 — Exponential-Density Realization & Unitary Connes Cocycle**:
   Defines `ExpDensityFactor n` (a Hermitian matrix `H : Matrix (Fin n) (Fin n) ℂ` yielding
   `ρ = exp H`, `r = exp ((1/2) • H)`, and `ρ^{it} = exp ((I * t) • H)`), embeds it into
   `PositiveComplexDensityFactor n` and `UnitaryFlow`,
   and constructs the unitary Connes Radon–Nikodym cocycle
   `relConnesCocycle E_ψ E_φ t = E_ψ.unitary t * E_φ.unitary (-t)` (`ρ_ψ^{it} ρ_φ^{-it}`),
   proving unitarity, the 1-cocycle law `u_{s+t} = u_s σ_s^φ(u_t)`, modular flow intertwining
   `σ_t^ψ(A) = u_t σ_t^φ(A) u_tᴴ`, the cocycle chain rule `u_{χ,φ}(t) = u_{χ,ψ}(t) u_{ψ,φ}(t)`,
   compatibility with `cocycleOfUnitaryFlows` and `cocycleDataOfUnitaryFlows`, and commutation of
   the relative modular unitary group `Δ_{ψ,φ}^{it}` with `Δ_{ψ,φ}`.

3. **Part 3 — Explicit Noncommuting `2 × 2` Witness & Honest Open Scope**:
   Constructs `witnessExpPhi, witnessExpPsi : ExpDensityFactor 2` via a rational `3/5, 4/5`
   unitary rotation of `diag(1, -1)` and proves `[ρ_ψ, ρ_φ] ≠ 0` (`witnessRhoPsi * witnessRhoPhi ≠
   witnessRhoPhi * witnessRhoPsi`) as well as non-scalarity and non-commutativity of the Connes
   cocycle at `t = π / 2`.

## Carrier Separation & Honest Scope Boundary
- **Real vs. Complex Carrier Separation**: Strictly separate from
  `InfoGeometry.Canonical.FiniteMatrixTomitaPolar` (which is scoped to real matrices
  `Matrix (Fin n) (Fin n) ℝ` with transpose `Xᵀ`).
- **Relation to `PedersenTakesakiRNInterface`**:
  `InfoGeometry.Canonical.PedersenTakesakiRNInterface.AffiliatedOperatorRNInterface` models an
  abstract real-Hilbert (`E`) interface carrying a scalar-id witness
  `delta = densityReadout • idEndH E`, and `PedersenTakesakiRNInterface.finiteAffiliatedDensity`
  is a diagonal real matrix on `PositiveRay (Fin n)`. Here we construct genuinely noncommuting
  complex operators on `Matrix (Fin n) (Fin n) ℂ`.
- **Open Scope**: Existence and uniqueness of unbounded affiliated relative modular operators and
  Pedersen–Takesaki / Vaes Radon–Nikodym derivatives on general infinite-dimensional von Neumann
  algebras remain outside the finite-dimensional matrix scope of this module.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Modular.ComplexRelativeModularRN

open Matrix Complex
open InfoGeometry.Modular.ComplexMatrixTomitaDuality
open InfoGeometry.Modular.ConnesCocycle
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics
open InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle

/-! =========================================================================
    1. Relative Tomita & Relative Modular Operators on `M_n(ℂ)`
    ========================================================================= -/

section RelativeTomitaModular

variable {n : ℕ}

/-- Relative modular operator `Δ_{ψ,φ}(X) = ρ_ψ X ρ_φ⁻¹` on `M_n(ℂ)`. -/
def relModularOp (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  F_ψ.rho * X * F_φ.rhoInv

/-- Inverse relative modular operator `Δ_{ψ,φ}⁻¹(X) = ρ_ψ⁻¹ X ρ_φ`. -/
def relModularInvOp (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  F_ψ.rhoInv * X * F_φ.rho

/-- Square root of the relative modular operator `Δ_{ψ,φ}^{1/2}(X) = r_ψ X r_φ⁻¹`. -/
def relModularSqrt (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  F_ψ.r * X * F_φ.rInv

/-- Inverse square root `Δ_{ψ,φ}^{-1/2}(X) = r_ψ⁻¹ X r_φ`. -/
def relModularInvSqrt (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  F_ψ.rInv * X * F_φ.r

/-- Relative Tomita operator `S_{ψ,φ}(X) = r_φ⁻¹ Xᴴ r_ψ` sending `A r_φ ↦ Aᴴ r_ψ`. -/
def relTomitaOp (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  F_φ.rInv * Xᴴ * F_ψ.r

/-- Hilbert–Schmidt adjoint `F_{ψ,φ}(X) = r_ψ Xᴴ r_φ⁻¹` of `S_{ψ,φ}`. -/
def relTomitaAdjOp (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  F_ψ.r * Xᴴ * F_φ.rInv

/-- Complex linear map bundling `Δ_{ψ,φ}^{1/2}`. -/
def relModularSqrtLinear (F_ψ F_φ : PositiveComplexDensityFactor n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := relModularSqrt F_ψ F_φ
  map_add' := fun X Y => by
    unfold relModularSqrt
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun c X => by
    unfold relModularSqrt
    rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- Complex linear map bundling `Δ_{ψ,φ}^{-1/2}`. -/
def relModularInvSqrtLinear (F_ψ F_φ : PositiveComplexDensityFactor n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := relModularInvSqrt F_ψ F_φ
  map_add' := fun X Y => by
    unfold relModularInvSqrt
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun c X => by
    unfold relModularInvSqrt
    rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- Complex linear map bundling `Δ_{ψ,φ}`. -/
def relModularOpLinear (F_ψ F_φ : PositiveComplexDensityFactor n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := relModularOp F_ψ F_φ
  map_add' := fun X Y => by
    unfold relModularOp
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun c X => by
    unfold relModularOp
    rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp]
theorem relTomitaOp_self (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F F X = tomitaOp F X := rfl

@[simp]
theorem relTomitaAdjOp_self (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaAdjOp F F X = tomitaAdjOp F X := rfl

@[simp]
theorem relModularOp_self (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularOp F F X = modularOp F X := rfl

@[simp]
theorem relModularSqrt_self (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularSqrt F F X = modularSqrt F X := rfl

/-- Relative Tomita action on cyclic coordinates: `S_{ψ,φ}(A r_φ) = Aᴴ r_ψ`. -/
theorem relTomitaOp_on_cyclic (F_ψ F_φ : PositiveComplexDensityFactor n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_ψ F_φ (A * F_φ.r) = Aᴴ * F_ψ.r := by
  unfold relTomitaOp
  rw [Matrix.conjTranspose_mul, F_φ.r_herm]
  calc
    F_φ.rInv * (F_φ.r * Aᴴ) * F_ψ.r = (F_φ.rInv * F_φ.r) * Aᴴ * F_ψ.r := by
      simp only [Matrix.mul_assoc]
    _ = Aᴴ * F_ψ.r := by rw [F_φ.rInv_mul_r, Matrix.one_mul]

/-- Relative Tomita maps the cyclic vector `r_φ` to `r_ψ`. -/
theorem relTomitaOp_cyclic (F_ψ F_φ : PositiveComplexDensityFactor n) :
    relTomitaOp F_ψ F_φ F_φ.r = F_ψ.r := by
  unfold relTomitaOp
  rw [F_φ.r_herm, F_φ.rInv_mul_r, Matrix.one_mul]

theorem relTomitaOp_add (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_ψ F_φ (X + Y) = relTomitaOp F_ψ F_φ X + relTomitaOp F_ψ F_φ Y := by
  unfold relTomitaOp
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem relTomitaOp_smul (F_ψ F_φ : PositiveComplexDensityFactor n)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_ψ F_φ (c • X) = star c • relTomitaOp F_ψ F_φ X := by
  unfold relTomitaOp
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- Swapping `ψ` and `φ` gives the inverse of `S_{ψ,φ}`: `S_{φ,ψ}(S_{ψ,φ}(X)) = X`. -/
theorem relTomitaOp_swap_involutive (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_φ F_ψ (relTomitaOp F_ψ F_φ X) = X := by
  unfold relTomitaOp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    F_ψ.r_herm, F_φ.rInv_herm]
  calc
    F_ψ.rInv * (F_ψ.r * (X * F_φ.rInv)) * F_φ.r
        = (F_ψ.rInv * F_ψ.r) * X * (F_φ.rInv * F_φ.r) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [F_ψ.rInv_mul_r, F_φ.rInv_mul_r, Matrix.one_mul, Matrix.mul_one]

theorem relTomitaAdjOp_add (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaAdjOp F_ψ F_φ (X + Y) = relTomitaAdjOp F_ψ F_φ X + relTomitaAdjOp F_ψ F_φ Y := by
  unfold relTomitaAdjOp
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem relTomitaAdjOp_smul (F_ψ F_φ : PositiveComplexDensityFactor n)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaAdjOp F_ψ F_φ (c • X) = star c • relTomitaAdjOp F_ψ F_φ X := by
  unfold relTomitaAdjOp
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- Swapping `ψ` and `φ` gives the inverse of `F_{ψ,φ}`: `F_{φ,ψ}(F_{ψ,φ}(X)) = X`. -/
theorem relTomitaAdjOp_swap_involutive (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaAdjOp F_φ F_ψ (relTomitaAdjOp F_ψ F_φ X) = X := by
  unfold relTomitaAdjOp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    F_φ.rInv_herm, F_ψ.r_herm]
  calc
    F_φ.r * (F_φ.rInv * (X * F_ψ.r)) * F_ψ.rInv
        = (F_φ.r * F_φ.rInv) * X * (F_ψ.r * F_ψ.rInv) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [F_φ.r_mul_rInv, F_ψ.r_mul_rInv, Matrix.one_mul, Matrix.mul_one]

/-- Polar decomposition `S_{ψ,φ} = J ∘ Δ_{ψ,φ}^{1/2}` on `M_n(ℂ)`. -/
theorem relTomitaOp_polar (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_ψ F_φ X = matrixJ n (relModularSqrt F_ψ F_φ X) := by
  unfold relTomitaOp relModularSqrt
  rw [matrixJ_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    F_ψ.r_herm, F_φ.rInv_herm, Matrix.mul_assoc]

/-- Adjoint composition `F_{ψ,φ} ∘ S_{ψ,φ} = Δ_{ψ,φ}`. -/
theorem relModularOp_eq_adj_comp_relTomita (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaAdjOp F_ψ F_φ (relTomitaOp F_ψ F_φ X) = relModularOp F_ψ F_φ X := by
  unfold relTomitaAdjOp relTomitaOp relModularOp
    PositiveComplexDensityFactor.rho PositiveComplexDensityFactor.rhoInv
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    F_ψ.r_herm, F_φ.rInv_herm]
  simp only [Matrix.mul_assoc]

/-- Reverse composition `S_{ψ,φ} ∘ F_{ψ,φ} = Δ_{φ,ψ}⁻¹`. -/
theorem relTomitaOp_comp_relTomitaAdjOp (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_ψ F_φ (relTomitaAdjOp F_ψ F_φ X) = relModularInvOp F_φ F_ψ X := by
  unfold relTomitaOp relTomitaAdjOp relModularInvOp
    PositiveComplexDensityFactor.rho PositiveComplexDensityFactor.rhoInv
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    F_φ.rInv_herm, F_ψ.r_herm]
  simp only [Matrix.mul_assoc]

/-- `Δ_{ψ,φ}^{1/2} ∘ Δ_{ψ,φ}^{1/2} = Δ_{ψ,φ}`. -/
theorem relModularSqrt_comp_self (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularSqrt F_ψ F_φ (relModularSqrt F_ψ F_φ X) = relModularOp F_ψ F_φ X := by
  unfold relModularSqrt relModularOp
    PositiveComplexDensityFactor.rho PositiveComplexDensityFactor.rhoInv
  simp only [Matrix.mul_assoc]

theorem relModularSqrt_comp_inv (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularSqrt F_ψ F_φ (relModularInvSqrt F_ψ F_φ X) = X := by
  unfold relModularSqrt relModularInvSqrt
  calc
    F_ψ.r * (F_ψ.rInv * X * F_φ.r) * F_φ.rInv
        = (F_ψ.r * F_ψ.rInv) * X * (F_φ.r * F_φ.rInv) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [F_ψ.r_mul_rInv, F_φ.r_mul_rInv, Matrix.one_mul, Matrix.mul_one]

theorem relModularInvSqrt_comp_sqrt (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularInvSqrt F_ψ F_φ (relModularSqrt F_ψ F_φ X) = X := by
  unfold relModularInvSqrt relModularSqrt
  calc
    F_ψ.rInv * (F_ψ.r * X * F_φ.rInv) * F_φ.r
        = (F_ψ.rInv * F_ψ.r) * X * (F_φ.rInv * F_φ.r) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [F_ψ.rInv_mul_r, F_φ.rInv_mul_r, Matrix.one_mul, Matrix.mul_one]

theorem relModularOp_comp_inv (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularOp F_ψ F_φ (relModularInvOp F_ψ F_φ X) = X := by
  unfold relModularOp relModularInvOp
  calc
    F_ψ.rho * (F_ψ.rhoInv * X * F_φ.rho) * F_φ.rhoInv
        = (F_ψ.rho * F_ψ.rhoInv) * X * (F_φ.rho * F_φ.rhoInv) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [F_ψ.rho_mul_rhoInv, F_φ.rho_mul_rhoInv, Matrix.one_mul, Matrix.mul_one]

theorem relModularInvOp_comp (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularInvOp F_ψ F_φ (relModularOp F_ψ F_φ X) = X := by
  unfold relModularInvOp relModularOp
  calc
    F_ψ.rhoInv * (F_ψ.rho * X * F_φ.rhoInv) * F_φ.rho
        = (F_ψ.rhoInv * F_ψ.rho) * X * (F_φ.rhoInv * F_φ.rho) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [F_ψ.rhoInv_mul_rho, F_φ.rhoInv_mul_rho, Matrix.one_mul, Matrix.mul_one]

/-- `J Δ_{ψ,φ} J = Δ_{φ,ψ}⁻¹` on `M_n(ℂ)`. -/
theorem matrixJ_relModularOp_conj (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixJ n (relModularOp F_ψ F_φ (matrixJ n X)) = relModularInvOp F_φ F_ψ X := by
  unfold relModularOp relModularInvOp
  rw [matrixJ_apply, matrixJ_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, F_ψ.rho_herm, F_φ.rhoInv_herm, Matrix.mul_assoc]

/-- Antilinear adjoint relation in the right slot: `⟨X, S_{ψ,φ} Y⟩_HS = ⟨Y, F_{ψ,φ} X⟩_HS`. -/
theorem hsInner_relTomitaOp_eq (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n X (relTomitaOp F_ψ F_φ Y) = hsInner n Y (relTomitaAdjOp F_ψ F_φ X) := by
  unfold hsInner relTomitaOp relTomitaAdjOp
  calc
    (Xᴴ * (F_φ.rInv * Yᴴ * F_ψ.r)).trace = ((Xᴴ * F_φ.rInv) * (Yᴴ * F_ψ.r)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((Yᴴ * F_ψ.r) * (Xᴴ * F_φ.rInv)).trace := Matrix.trace_mul_comm _ _
    _ = (Yᴴ * (F_ψ.r * Xᴴ * F_φ.rInv)).trace := by simp only [Matrix.mul_assoc]

/-- Antilinear adjoint relation in the left slot: `⟨S_{ψ,φ} X, Y⟩_HS = ⟨F_{ψ,φ} Y, X⟩_HS`. -/
theorem hsInner_relTomitaOp_left_eq (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n (relTomitaOp F_ψ F_φ X) Y = hsInner n (relTomitaAdjOp F_ψ F_φ Y) X := by
  have h := hsInner_relTomitaOp_eq F_ψ F_φ Y X
  have hstar := congrArg star h
  simpa only [hsInner_conj_symm] using hstar

/-- Hilbert–Schmidt self-adjointness of `Δ_{ψ,φ}`: `⟨X, Δ_{ψ,φ} Y⟩_HS = ⟨Δ_{ψ,φ} X, Y⟩_HS`. -/
theorem relModularOp_hsSelfAdjoint (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n X (relModularOp F_ψ F_φ Y) = hsInner n (relModularOp F_ψ F_φ X) Y := by
  unfold hsInner relModularOp
  have hL :
      (Xᴴ * (F_ψ.rho * Y * F_φ.rhoInv)).trace =
        (F_φ.rhoInv * Xᴴ * F_ψ.rho * Y).trace := by
    calc
      (Xᴴ * (F_ψ.rho * Y * F_φ.rhoInv)).trace
          = ((Xᴴ * F_ψ.rho * Y) * F_φ.rhoInv).trace := by
        simp only [Matrix.mul_assoc]
      _ = (F_φ.rhoInv * (Xᴴ * F_ψ.rho * Y)).trace := Matrix.trace_mul_comm _ _
      _ = (F_φ.rhoInv * Xᴴ * F_ψ.rho * Y).trace := by simp only [Matrix.mul_assoc]
  have hR :
      ((F_ψ.rho * X * F_φ.rhoInv)ᴴ * Y).trace =
        (F_φ.rhoInv * Xᴴ * F_ψ.rho * Y).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, F_ψ.rho_herm, F_φ.rhoInv_herm]
    simp only [Matrix.mul_assoc]
  exact hL.trans hR.symm

/-- Exact sesquilinearly consistent quadratic identity for `S_{ψ,φ}` and `Δ_{ψ,φ}`:
`⟨S_{ψ,φ} X, S_{ψ,φ} Y⟩_HS = ⟨Y, Δ_{ψ,φ} X⟩_HS`. -/
theorem hsInner_relTomitaOp_quadratic (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n (relTomitaOp F_ψ F_φ X) (relTomitaOp F_ψ F_φ Y) =
      hsInner n Y (relModularOp F_ψ F_φ X) := by
  rw [hsInner_relTomitaOp_eq, relModularOp_eq_adj_comp_relTomita]

/-- Factorization `⟨X, Δ_{ψ,φ} Y⟩_HS = ⟨Δ_{ψ,φ}^{1/2} X, Δ_{ψ,φ}^{1/2} Y⟩_HS`. -/
theorem hsInner_relModularOp_eq_hsInner_sqrt (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n X (relModularOp F_ψ F_φ Y) =
      hsInner n (relModularSqrt F_ψ F_φ X) (relModularSqrt F_ψ F_φ Y) := by
  unfold hsInner relModularOp relModularSqrt
    PositiveComplexDensityFactor.rho PositiveComplexDensityFactor.rhoInv
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, F_ψ.r_herm, F_φ.rInv_herm]
  calc
    (Xᴴ * (F_ψ.r * F_ψ.r * Y * (F_φ.rInv * F_φ.rInv))).trace
        = (((F_φ.rInv * Xᴴ * F_ψ.r) * (F_ψ.r * Y * F_φ.rInv))).trace := by
      have hcomm :
          ((Xᴴ * (F_ψ.r * F_ψ.r * Y * F_φ.rInv)) * F_φ.rInv).trace =
            (F_φ.rInv * (Xᴴ * (F_ψ.r * F_ψ.r * Y * F_φ.rInv))).trace :=
        Matrix.trace_mul_comm _ _
      simpa only [Matrix.mul_assoc] using hcomm
    _ = ((F_φ.rInv * (Xᴴ * F_ψ.r)) * (F_ψ.r * Y * F_φ.rInv)).trace := by
      simp only [Matrix.mul_assoc]

/-- Real nonnegativity of the complex Hilbert–Schmidt norm squared `(⟨X, X⟩_HS).re ≥ 0`. -/
theorem hsInner_self_re_nonneg (X : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (hsInner n X X).re := by
  unfold hsInner
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Faithfulness of the complex Hilbert–Schmidt inner product: `⟨X, X⟩_HS = 0 ↔ X = 0`. -/
theorem hsInner_self_eq_zero_iff (X : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hre : (hsInner n X X).re = 0 := by rw [h]; simp
    have hsum : ∑ i : Fin n, ∑ j : Fin n, ‖X j i‖ ^ 2 = 0 := by
      have hcalc :
          (hsInner n X X).re = ∑ i : Fin n, ∑ j : Fin n, ‖X j i‖ ^ 2 := by
        unfold hsInner
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Complex.re_sum, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
          Complex.ofReal_re]
      rw [← hcalc, hre]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hsum
    ext j i
    have hi := hsum i (Finset.mem_univ i)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at hi
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hi j (Finset.mem_univ j)))
  · rintro rfl
    simp [hsInner]

/-- Positivity of `Δ_{ψ,φ}`: `0 ≤ (⟨X, Δ_{ψ,φ} X⟩_HS).re`. -/
theorem relModularOp_hsPos_re_nonneg (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (hsInner n X (relModularOp F_ψ F_φ X)).re := by
  rw [hsInner_relModularOp_eq_hsInner_sqrt]
  exact hsInner_self_re_nonneg (relModularSqrt F_ψ F_φ X)

/-- Strict positivity (faithfulness) of `Δ_{ψ,φ}`: `⟨X, Δ_{ψ,φ} X⟩_HS = 0 ↔ X = 0`. -/
theorem relModularOp_hsPos_eq_zero_iff (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n X (relModularOp F_ψ F_φ X) = 0 ↔ X = 0 := by
  rw [hsInner_relModularOp_eq_hsInner_sqrt, hsInner_self_eq_zero_iff]
  constructor
  · intro h
    calc
      X = relModularInvSqrt F_ψ F_φ (relModularSqrt F_ψ F_φ X) :=
        (relModularInvSqrt_comp_sqrt F_ψ F_φ X).symm
      _ = relModularInvSqrt F_ψ F_φ 0 := by rw [h]
      _ = 0 := by simp [relModularInvSqrt]
  · rintro rfl
    simp [relModularSqrt]

/-- Two-state relative KMS cyclicity: `ω_φ(A Δ_{ψ,φ}(B)) = ω_ψ(B A)`. -/
theorem relModularOp_kms_identity (F_ψ F_φ : PositiveComplexDensityFactor n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    state F_φ (A * relModularOp F_ψ F_φ B) = state F_ψ (B * A) := by
  unfold state relModularOp
  calc
    (F_φ.rho * (A * (F_ψ.rho * B * F_φ.rhoInv))).trace
        = ((F_φ.rho * A * F_ψ.rho * B) * F_φ.rhoInv).trace := by
      simp only [Matrix.mul_assoc]
    _ = (F_φ.rhoInv * (F_φ.rho * A * F_ψ.rho * B)).trace := Matrix.trace_mul_comm _ _
    _ = ((F_φ.rhoInv * F_φ.rho) * A * F_ψ.rho * B).trace := by
      simp only [Matrix.mul_assoc]
    _ = (A * (F_ψ.rho * B)).trace := by
      rw [F_φ.rhoInv_mul_rho, Matrix.one_mul, Matrix.mul_assoc]
    _ = (F_ψ.rho * (B * A)).trace := by
      rw [Matrix.trace_mul_comm A (F_ψ.rho * B), Matrix.mul_assoc]

end RelativeTomitaModular

/-! =========================================================================
    2. Exponential-Density Realization & Unitary Connes RN Cocycle
    ========================================================================= -/

/-- A unitary one-parameter group in a star monoid (`u(s+t) = u s * u t`, `u 0 = 1`). -/
structure UnitaryFlow (A : Type*) [Monoid A] [StarMul A] where
  u : ℝ → A
  map_zero : u 0 = 1
  map_add : ∀ s t, u (s + t) = u s * u t
  unitary_left : ∀ t, u t * star (u t) = 1
  unitary_right : ∀ t, star (u t) * u t = 1

instance instInhabitedUnitaryFlow {A : Type*} [Monoid A] [StarMul A] :
    Inhabited (UnitaryFlow A) where
  default :=
    { u := fun _ => 1
      map_zero := rfl
      map_add := fun _ _ => (mul_one (1 : A)).symm
      unitary_left := fun _ => by simp
      unitary_right := fun _ => by simp }

section UnitaryFlowInterfaces

/-- Spatial conjugation of an algebra element by a unitary. -/
def conjStarAlgHom {A : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
    (u : A) (huL : u * star u = 1) (huR : star u * u = 1) :
    A →⋆ₐ[ℂ] A where
  toFun x := u * x * star u
  map_one' := by simpa using huL
  map_mul' x y := by
    change u * (x * y) * star u = (u * x * star u) * (u * y * star u)
    calc
      u * (x * y) * star u = u * x * (1 * y) * star u := by simp [mul_assoc]
      _ = u * x * ((star u * u) * y) * star u := by rw [huR]
      _ = (u * x * star u) * (u * y * star u) := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' c := by
    change u * algebraMap ℂ A c * star u = algebraMap ℂ A c
    rw [← Algebra.commutes c u, mul_assoc, huL, mul_one]
  map_star' x := by
    simp [star_mul, mul_assoc]

/-- The modular flow `Ad(u_t)` of a unitary flow. -/
def modularFlowOfUnitary {A : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
    (U : UnitaryFlow A) : ModularFlow ℂ A where
  toFun t := conjStarAlgHom (U.u t) (U.unitary_left t) (U.unitary_right t)
  map_zero := by
    ext x
    change U.u 0 * x * star (U.u 0) = x
    simp [U.map_zero]
  map_add s t := by
    intro x
    change U.u (s + t) * x * star (U.u (s + t)) =
      U.u s * (U.u t * x * star (U.u t)) * star (U.u s)
    rw [U.map_add s t, star_mul]
    simp [mul_assoc]

/-- The noncommuting Connes cocycle `u_t = uψ_t (uφ_t)*`. -/
def cocycleOfUnitaryFlows {A : Type*} [Semiring A] [StarRing A] [Algebra ℂ A]
    (φ ψ : UnitaryFlow A) :
    ConnesOneCocycle (modularFlowOfUnitary φ) where
  u t := ψ.u t * star (φ.u t)
  cocycle_id s t := by
    dsimp [modularFlowOfUnitary, conjStarAlgHom]
    rw [ψ.map_add s t, φ.map_add s t, star_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (star (φ.u s)) (φ.u s), φ.unitary_right s, one_mul]
  cocycle_zero := by
    simp [ψ.map_zero, φ.map_zero]
  unitary_left t := by
    simp only [star_mul, star_star]
    rw [mul_assoc, ← mul_assoc (star (φ.u t)) (φ.u t), φ.unitary_right t, one_mul,
      ψ.unitary_left t]
  unitary_right t := by
    simp only [star_mul, star_star]
    rw [mul_assoc, ← mul_assoc (star (ψ.u t)) (ψ.u t), ψ.unitary_right t, one_mul,
      φ.unitary_left t]

/-- Multiplicative equivalence `x ↦ u x u*` induced by a unitary element. -/
def conjMulEquiv {A : Type*} [Monoid A] [StarMul A]
    (u : A) (huL : u * star u = 1) (huR : star u * u = 1) : A ≃* A where
  toFun x := u * x * star u
  invFun x := star u * x * u
  left_inv x := by
    calc
      star u * (u * x * star u) * u = (star u * u) * x * (star u * u) := by
        simp only [mul_assoc]
      _ = x := by rw [huR, one_mul, mul_one]
  right_inv x := by
    calc
      u * (star u * x * u) * star u = (u * star u) * x * (u * star u) := by
        simp only [mul_assoc]
      _ = x := by rw [huL, one_mul, mul_one]
  map_mul' x y := by
    calc
      u * (x * y) * star u = u * x * (1 * y) * star u := by simp [mul_assoc]
      _ = u * x * ((star u * u) * y) * star u := by rw [huR]
      _ = (u * x * star u) * (u * y * star u) := by simp only [mul_assoc]

/-- The `OperatorFlow` of spatial conjugation by a unitary flow. -/
def operatorFlowOfUnitary {A : Type*} [Monoid A] [StarMul A]
    (U : UnitaryFlow A) : OperatorFlow A where
  flow t := conjMulEquiv (U.u t) (U.unitary_left t) (U.unitary_right t)
  flow_zero x := by
    change U.u 0 * x * star (U.u 0) = x
    simp [U.map_zero]
  flow_add s t x := by
    change U.u (s + t) * x * star (U.u (s + t)) =
      U.u s * (U.u t * x * star (U.u t)) * star (U.u s)
    rw [U.map_add s t, star_mul]
    simp [mul_assoc]

/-- Concrete cocycle data on `A`, flows ordered as `(σ^ψ, σ^φ)`. -/
def cocycleDataOfUnitaryFlows {A : Type*} [Monoid A] [StarMul A]
    (φ ψ : UnitaryFlow A) :
    ConnesCocycleData A (operatorFlowOfUnitary ψ) (operatorFlowOfUnitary φ) where
  u t := ψ.u t * star (φ.u t)

theorem cocycleDataOfUnitaryFlows_isConnesCocycle {A : Type*} [Monoid A] [StarMul A]
    (φ ψ : UnitaryFlow A) :
    IsConnesCocycle (cocycleDataOfUnitaryFlows φ ψ) := by
  intro s t
  change ψ.u (s + t) * star (φ.u (s + t)) =
    (ψ.u s * star (φ.u s)) *
      (φ.u s * (ψ.u t * star (φ.u t)) * star (φ.u s))
  rw [ψ.map_add s t, φ.map_add s t, star_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (star (φ.u s)) (φ.u s), φ.unitary_right s, one_mul]

theorem cocycleDataOfUnitaryFlows_intertwines {A : Type*} [Monoid A] [StarMul A]
    (φ ψ : UnitaryFlow A) :
    Intertwines (cocycleDataOfUnitaryFlows φ ψ) := by
  intro t x
  change (ψ.u t * x * star (ψ.u t)) * (ψ.u t * star (φ.u t)) =
    (ψ.u t * star (φ.u t)) * (φ.u t * x * star (φ.u t))
  calc
    (ψ.u t * x * star (ψ.u t)) * (ψ.u t * star (φ.u t))
        = ψ.u t * x * (star (ψ.u t) * ψ.u t) * star (φ.u t) := by
      simp only [mul_assoc]
    _ = ψ.u t * x * star (φ.u t) := by rw [ψ.unitary_right t, mul_one]
    _ = ψ.u t * (1 * x) * star (φ.u t) := by rw [one_mul]
    _ = ψ.u t * ((star (φ.u t) * φ.u t) * x) * star (φ.u t) := by
      rw [φ.unitary_right t]
    _ = (ψ.u t * star (φ.u t)) * (φ.u t * x * star (φ.u t)) := by
      simp only [mul_assoc]

end UnitaryFlowInterfaces

/-- Invertible positive matrix density realized exponentially as `ρ = exp H` for a Hermitian
generator `H : Matrix (Fin n) (Fin n) ℂ`. -/
structure ExpDensityFactor (n : ℕ) where
  H : Matrix (Fin n) (Fin n) ℂ
  H_herm : H.IsHermitian

instance (n : ℕ) : Inhabited (ExpDensityFactor n) where
  default := { H := 0, H_herm := Matrix.isHermitian_zero }

namespace ExpDensityFactor

section ExponentialStructure

variable {n : ℕ}

/-- Density matrix `ρ = exp H`. -/
def rho (E : ExpDensityFactor n) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp E.H

/-- Inverse density matrix `ρ⁻¹ = exp (-H)`. -/
def rhoInv (E : ExpDensityFactor n) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (-E.H)

/-- Positive square root `r = ρ^{1/2} = exp ((1/2) • H)`. -/
def r (E : ExpDensityFactor n) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((1 / 2 : ℝ) • E.H)

/-- Inverse square root `r⁻¹ = ρ^{-1/2} = exp (-(1/2) • H)`. -/
def rInv (E : ExpDensityFactor n) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((-(1 / 2 : ℝ)) • E.H)

theorem r_eq_complex_smul (E : ExpDensityFactor n) :
    E.r = NormedSpace.exp ((1 / 2 : ℂ) • E.H) := by
  unfold r
  have hsmul : ((1 / 2 : ℝ) • E.H) = ((1 / 2 : ℂ) • E.H) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    rfl
  rw [hsmul]

/-- Unitary one-parameter power group `ρ^{it} = exp (i t H)`. -/
def unitary (E : ExpDensityFactor n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • E.H)

theorem r_herm (E : ExpDensityFactor n) : E.rᴴ = E.r := by
  unfold r
  rw [← Matrix.exp_conjTranspose]
  congr 1
  change star ((1 / 2 : ℝ) • E.H) = (1 / 2 : ℝ) • E.H
  rw [star_smul, star_trivial, Matrix.star_eq_conjTranspose, E.H_herm.eq]

theorem rInv_herm (E : ExpDensityFactor n) : E.rInvᴴ = E.rInv := by
  unfold rInv
  rw [← Matrix.exp_conjTranspose]
  congr 1
  change star ((-(1 / 2 : ℝ)) • E.H) = (-(1 / 2 : ℝ)) • E.H
  rw [star_smul, star_trivial, Matrix.star_eq_conjTranspose, E.H_herm.eq]

theorem r_mul_rInv (E : ExpDensityFactor n) : E.r * E.rInv = 1 := by
  unfold r rInv
  have hcomm : Commute ((1 / 2 : ℝ) • E.H) ((-(1 / 2 : ℝ)) • E.H) :=
    ((Commute.refl E.H).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul, add_neg_cancel, zero_smul,
    NormedSpace.exp_zero]

theorem rInv_mul_r (E : ExpDensityFactor n) : E.rInv * E.r = 1 := by
  unfold r rInv
  have hcomm : Commute ((-(1 / 2 : ℝ)) • E.H) ((1 / 2 : ℝ) • E.H) :=
    ((Commute.refl E.H).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul, neg_add_cancel, zero_smul,
    NormedSpace.exp_zero]

theorem r_mul_r (E : ExpDensityFactor n) : E.r * E.r = E.rho := by
  unfold r rho
  have hcomm : Commute ((1 / 2 : ℝ) • E.H) ((1 / 2 : ℝ) • E.H) :=
    ((Commute.refl E.H).smul_left _).smul_right _
  have hhalf : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul, hhalf, one_smul]

theorem rInv_mul_rInv (E : ExpDensityFactor n) : E.rInv * E.rInv = E.rhoInv := by
  unfold rInv rhoInv
  have hcomm : Commute ((-(1 / 2 : ℝ)) • E.H) ((-(1 / 2 : ℝ)) • E.H) :=
    ((Commute.refl E.H).smul_left _).smul_right _
  have hhalf : -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 := by norm_num
  rw [← Matrix.exp_add_of_commute _ _ hcomm, ← add_smul, hhalf, neg_smul, one_smul]

/-- Canonical embedding of `ExpDensityFactor n` into `PositiveComplexDensityFactor n`. -/
def toPositiveComplexDensityFactor (E : ExpDensityFactor n) : PositiveComplexDensityFactor n where
  r := E.r
  rInv := E.rInv
  r_herm := E.r_herm
  rInv_herm := E.rInv_herm
  r_mul_rInv := E.r_mul_rInv
  rInv_mul_r := E.rInv_mul_r

@[simp]
theorem toPositiveComplexDensityFactor_rho (E : ExpDensityFactor n) :
    E.toPositiveComplexDensityFactor.rho = E.rho :=
  E.r_mul_r

@[simp]
theorem toPositiveComplexDensityFactor_rhoInv (E : ExpDensityFactor n) :
    E.toPositiveComplexDensityFactor.rhoInv = E.rhoInv :=
  E.rInv_mul_rInv

@[simp]
theorem unitary_zero (E : ExpDensityFactor n) : E.unitary 0 = 1 := by
  simp [unitary]

theorem unitary_add (E : ExpDensityFactor n) (s t : ℝ) :
    E.unitary (s + t) = E.unitary s * E.unitary t := by
  unfold unitary
  have hsc : Complex.I * ((s + t : ℝ) : ℂ) = Complex.I * (s : ℂ) + Complex.I * (t : ℂ) := by
    push_cast
    ring
  have hcomm : Commute ((Complex.I * (s : ℂ)) • E.H) ((Complex.I * (t : ℂ)) • E.H) :=
    ((Commute.refl E.H).smul_left _).smul_right _
  rw [hsc, add_smul, Matrix.exp_add_of_commute _ _ hcomm]

theorem unitary_conjTranspose (E : ExpDensityFactor n) (t : ℝ) :
    (E.unitary t)ᴴ = E.unitary (-t) := by
  unfold unitary
  rw [← Matrix.exp_conjTranspose]
  congr 1
  change star ((Complex.I * (t : ℂ)) • E.H) = (Complex.I * ((-t : ℝ) : ℂ)) • E.H
  rw [star_smul, Matrix.star_eq_conjTranspose, E.H_herm.eq]
  congr 1
  rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem unitary_mul_neg (E : ExpDensityFactor n) (t : ℝ) :
    E.unitary t * E.unitary (-t) = 1 := by
  rw [← E.unitary_add t (-t), add_neg_cancel, E.unitary_zero]

theorem unitary_neg_mul (E : ExpDensityFactor n) (t : ℝ) :
    E.unitary (-t) * E.unitary t = 1 := by
  rw [← E.unitary_add (-t) t, neg_add_cancel, E.unitary_zero]

theorem rho_commute_unitary (E : ExpDensityFactor n) (t : ℝ) :
    Commute E.rho (E.unitary t) := by
  unfold rho unitary Commute SemiconjBy
  have hcomm1 : Commute E.H ((Complex.I * (t : ℂ)) • E.H) :=
    (Commute.refl E.H).smul_right _
  have hcomm2 : Commute ((Complex.I * (t : ℂ)) • E.H) E.H := hcomm1.symm
  rw [← Matrix.exp_add_of_commute _ _ hcomm1, ← Matrix.exp_add_of_commute _ _ hcomm2, add_comm]

theorem rhoInv_commute_unitary (E : ExpDensityFactor n) (t : ℝ) :
    Commute E.rhoInv (E.unitary t) := by
  unfold rhoInv unitary Commute SemiconjBy
  have hcomm1 : Commute (-E.H) ((Complex.I * (t : ℂ)) • E.H) :=
    ((Commute.refl E.H).neg_left).smul_right _
  have hcomm2 : Commute ((Complex.I * (t : ℂ)) • E.H) (-E.H) := hcomm1.symm
  rw [← Matrix.exp_add_of_commute _ _ hcomm1, ← Matrix.exp_add_of_commute _ _ hcomm2, add_comm]

theorem r_commute_unitary (E : ExpDensityFactor n) (t : ℝ) :
    Commute E.r (E.unitary t) := by
  unfold r unitary Commute SemiconjBy
  have hcomm1 : Commute ((1 / 2 : ℝ) • E.H) ((Complex.I * (t : ℂ)) • E.H) :=
    ((Commute.refl E.H).smul_left _).smul_right _
  have hcomm2 : Commute ((Complex.I * (t : ℂ)) • E.H) ((1 / 2 : ℝ) • E.H) := hcomm1.symm
  rw [← Matrix.exp_add_of_commute _ _ hcomm1, ← Matrix.exp_add_of_commute _ _ hcomm2, add_comm]

/-- `UnitaryFlow` induced by `t ↦ ρ^{it}` on `M_n(ℂ)`. -/
def unitaryFlow (E : ExpDensityFactor n) : UnitaryFlow (Matrix (Fin n) (Fin n) ℂ) where
  u := E.unitary
  map_zero := E.unitary_zero
  map_add := E.unitary_add
  unitary_left := fun t => by
    change E.unitary t * (E.unitary t)ᴴ = 1
    rw [E.unitary_conjTranspose, E.unitary_mul_neg]
  unitary_right := fun t => by
    change (E.unitary t)ᴴ * E.unitary t = 1
    rw [E.unitary_conjTranspose, E.unitary_neg_mul]

/-- Modular automorphism group `σ_t^φ(A) = ρ^{it} A ρ^{-it}` as a `ModularFlow`. -/
def modularFlow (E : ExpDensityFactor n) : ModularFlow ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  modularFlowOfUnitary E.unitaryFlow

@[simp]
theorem modularFlow_apply (E : ExpDensityFactor n) (t : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    E.modularFlow t A = E.unitary t * A * E.unitary (-t) := by
  dsimp [modularFlow, modularFlowOfUnitary, conjStarAlgHom, unitaryFlow]
  rw [Matrix.star_eq_conjTranspose, E.unitary_conjTranspose]

/-- Operator flow `σ_t^φ` in `ConstructiveConnesCocycle` interface. -/
def operatorFlow (E : ExpDensityFactor n) : OperatorFlow (Matrix (Fin n) (Fin n) ℂ) :=
  operatorFlowOfUnitary E.unitaryFlow

@[simp]
theorem operatorFlow_apply (E : ExpDensityFactor n) (t : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    E.operatorFlow.flow t A = E.unitary t * A * E.unitary (-t) := by
  change E.unitary t * A * (E.unitary t)ᴴ = E.unitary t * A * E.unitary (-t)
  rw [E.unitary_conjTranspose]

end ExponentialStructure

end ExpDensityFactor

section ConnesCocycleBridge

variable {n : ℕ}

/-- Unitary Connes Radon–Nikodym cocycle `(Dψ : Dφ)_t = ρ_ψ^{it} ρ_φ^{-it}`. -/
def relConnesCocycle (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  E_ψ.unitary t * E_φ.unitary (-t)

theorem relConnesCocycle_eq_cocycleOfUnitaryFlows (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    (cocycleOfUnitaryFlows E_φ.unitaryFlow E_ψ.unitaryFlow).u t =
      relConnesCocycle E_ψ E_φ t := by
  change E_ψ.unitary t * (E_φ.unitary t)ᴴ = E_ψ.unitary t * E_φ.unitary (-t)
  rw [E_φ.unitary_conjTranspose]

theorem relConnesCocycle_eq_cocycleDataOfUnitaryFlows (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    (cocycleDataOfUnitaryFlows E_φ.unitaryFlow E_ψ.unitaryFlow).u t =
      relConnesCocycle E_ψ E_φ t := by
  change E_ψ.unitary t * (E_φ.unitary t)ᴴ = E_ψ.unitary t * E_φ.unitary (-t)
  rw [E_φ.unitary_conjTranspose]

@[simp]
theorem relConnesCocycle_zero (E_ψ E_φ : ExpDensityFactor n) :
    relConnesCocycle E_ψ E_φ 0 = 1 := by
  simp [relConnesCocycle]

theorem relConnesCocycle_conjTranspose (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    (relConnesCocycle E_ψ E_φ t)ᴴ = relConnesCocycle E_φ E_ψ t := by
  unfold relConnesCocycle
  rw [Matrix.conjTranspose_mul, E_φ.unitary_conjTranspose, E_ψ.unitary_conjTranspose, neg_neg]

theorem relConnesCocycle_unitary_left (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    relConnesCocycle E_ψ E_φ t * (relConnesCocycle E_ψ E_φ t)ᴴ = 1 := by
  rw [relConnesCocycle_conjTranspose]
  unfold relConnesCocycle
  calc
    (E_ψ.unitary t * E_φ.unitary (-t)) * (E_φ.unitary t * E_ψ.unitary (-t))
        = E_ψ.unitary t * (E_φ.unitary (-t) * E_φ.unitary t) * E_ψ.unitary (-t) := by
      simp only [Matrix.mul_assoc]
    _ = E_ψ.unitary t * E_ψ.unitary (-t) := by
      rw [E_φ.unitary_neg_mul, Matrix.mul_one]
    _ = 1 := E_ψ.unitary_mul_neg t

theorem relConnesCocycle_unitary_right (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    (relConnesCocycle E_ψ E_φ t)ᴴ * relConnesCocycle E_ψ E_φ t = 1 := by
  rw [relConnesCocycle_conjTranspose]
  unfold relConnesCocycle
  calc
    (E_φ.unitary t * E_ψ.unitary (-t)) * (E_ψ.unitary t * E_φ.unitary (-t))
        = E_φ.unitary t * (E_ψ.unitary (-t) * E_ψ.unitary t) * E_φ.unitary (-t) := by
      simp only [Matrix.mul_assoc]
    _ = E_φ.unitary t * E_φ.unitary (-t) := by
      rw [E_ψ.unitary_neg_mul, Matrix.mul_one]
    _ = 1 := E_φ.unitary_mul_neg t

/-- Connes 1-cocycle identity `u_{s+t} = u_s * σ_s^φ(u_t)`. -/
theorem relConnesCocycle_cocycle_id (E_ψ E_φ : ExpDensityFactor n) (s t : ℝ) :
    relConnesCocycle E_ψ E_φ (s + t) =
      relConnesCocycle E_ψ E_φ s * E_φ.modularFlow s (relConnesCocycle E_ψ E_φ t) := by
  unfold ExpDensityFactor.modularFlow
  simpa only [relConnesCocycle_eq_cocycleOfUnitaryFlows] using
    (cocycleOfUnitaryFlows E_φ.unitaryFlow E_ψ.unitaryFlow).cocycle_id s t

/-- Connes flow intertwining `σ_t^ψ(A) = u_t * σ_t^φ(A) * u_tᴴ`. -/
theorem relConnesCocycle_intertwines (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    E_ψ.modularFlow t A =
      relConnesCocycle E_ψ E_φ t * E_φ.modularFlow t A * (relConnesCocycle E_ψ E_φ t)ᴴ := by
  rw [E_ψ.modularFlow_apply, E_φ.modularFlow_apply, relConnesCocycle_conjTranspose]
  unfold relConnesCocycle
  calc
    E_ψ.unitary t * A * E_ψ.unitary (-t)
        = (E_ψ.unitary t * (E_φ.unitary (-t) * E_φ.unitary t) * A *
          (E_φ.unitary (-t) * E_φ.unitary t)) * E_ψ.unitary (-t) := by
      simp only [E_φ.unitary_neg_mul, Matrix.mul_one]
    _ = (E_ψ.unitary t * E_φ.unitary (-t)) * (E_φ.unitary t * A * E_φ.unitary (-t)) *
          (E_φ.unitary t * E_ψ.unitary (-t)) := by
      simp only [Matrix.mul_assoc]

/-- Connes cocycle chain rule `(Dχ : Dφ)_t = (Dχ : Dψ)_t * (Dψ : Dφ)_t`. -/
theorem relConnesCocycle_chain_rule (E_χ E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    relConnesCocycle E_χ E_φ t =
      relConnesCocycle E_χ E_ψ t * relConnesCocycle E_ψ E_φ t := by
  unfold relConnesCocycle
  calc
    E_χ.unitary t * E_φ.unitary (-t)
        = E_χ.unitary t * (E_ψ.unitary (-t) * E_ψ.unitary t) * E_φ.unitary (-t) := by
      rw [E_ψ.unitary_neg_mul, Matrix.mul_one]
    _ = (E_χ.unitary t * E_ψ.unitary (-t)) * (E_ψ.unitary t * E_φ.unitary (-t)) := by
      simp only [Matrix.mul_assoc]

theorem relConnesCocycle_cocycleData_isConnesCocycle (E_ψ E_φ : ExpDensityFactor n) :
    IsConnesCocycle (cocycleDataOfUnitaryFlows E_φ.unitaryFlow E_ψ.unitaryFlow) :=
  cocycleDataOfUnitaryFlows_isConnesCocycle E_φ.unitaryFlow E_ψ.unitaryFlow

theorem relConnesCocycle_cocycleData_intertwines (E_ψ E_φ : ExpDensityFactor n) :
    Intertwines (cocycleDataOfUnitaryFlows E_φ.unitaryFlow E_ψ.unitaryFlow) :=
  cocycleDataOfUnitaryFlows_intertwines E_φ.unitaryFlow E_ψ.unitaryFlow

/-- Relative modular unitary group `Δ_{ψ,φ}^{it}(X) = ρ_ψ^{it} X ρ_φ^{-it}` on `M_n(ℂ)`. -/
def relModularUnitary (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  E_ψ.unitary t * X * E_φ.unitary (-t)

@[simp]
theorem relModularUnitary_zero (E_ψ E_φ : ExpDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularUnitary E_ψ E_φ 0 X = X := by
  simp [relModularUnitary]

theorem relModularUnitary_add (E_ψ E_φ : ExpDensityFactor n) (s t : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularUnitary E_ψ E_φ (s + t) X =
      relModularUnitary E_ψ E_φ s (relModularUnitary E_ψ E_φ t X) := by
  unfold relModularUnitary
  have hneg : -(s + t) = -t + -s := by ring
  rw [E_ψ.unitary_add s t, hneg, E_φ.unitary_add (-t) (-s)]
  simp only [Matrix.mul_assoc]

/-- `Δ_{ψ,φ}^{it}` is unitary for the complex Hilbert–Schmidt inner product. -/
theorem hsInner_relModularUnitary (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n (relModularUnitary E_ψ E_φ t X) (relModularUnitary E_ψ E_φ t Y) =
      hsInner n X Y := by
  unfold hsInner relModularUnitary
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    E_φ.unitary_conjTranspose, E_ψ.unitary_conjTranspose, neg_neg]
  calc
    ((E_φ.unitary t * (Xᴴ * E_ψ.unitary (-t))) * (E_ψ.unitary t * Y * E_φ.unitary (-t))).trace
        = (E_φ.unitary t * (Xᴴ * (E_ψ.unitary (-t) * E_ψ.unitary t) * Y) *
          E_φ.unitary (-t)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((E_φ.unitary t * (Xᴴ * Y)) * E_φ.unitary (-t)).trace := by
      rw [E_ψ.unitary_neg_mul, Matrix.mul_one]
    _ = (E_φ.unitary (-t) * (E_φ.unitary t * (Xᴴ * Y))).trace := Matrix.trace_mul_comm _ _
    _ = ((E_φ.unitary (-t) * E_φ.unitary t) * (Xᴴ * Y)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (Xᴴ * Y).trace := by rw [E_φ.unitary_neg_mul, Matrix.one_mul]

/-- The Connes cocycle is recovered by evaluating `Δ_{ψ,φ}^{it}` at the identity:
`Δ_{ψ,φ}^{it}(1) = u_t`. -/
theorem relModularUnitary_one_eq_cocycle (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    relModularUnitary E_ψ E_φ t 1 = relConnesCocycle E_ψ E_φ t := by
  simp [relModularUnitary, relConnesCocycle]

theorem relModularUnitary_eq_cocycle_mul_modularFlow (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularUnitary E_ψ E_φ t X = relConnesCocycle E_ψ E_φ t * E_φ.modularFlow t X := by
  rw [E_φ.modularFlow_apply]
  unfold relModularUnitary relConnesCocycle
  calc
    E_ψ.unitary t * X * E_φ.unitary (-t)
        = E_ψ.unitary t * (E_φ.unitary (-t) * E_φ.unitary t) * X * E_φ.unitary (-t) := by
      rw [E_φ.unitary_neg_mul, Matrix.mul_one]
    _ = (E_ψ.unitary t * E_φ.unitary (-t)) * (E_φ.unitary t * X * E_φ.unitary (-t)) := by
      simp only [Matrix.mul_assoc]

theorem relModularUnitary_eq_modularFlow_mul_cocycle (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularUnitary E_ψ E_φ t X = E_ψ.modularFlow t X * relConnesCocycle E_ψ E_φ t := by
  rw [E_ψ.modularFlow_apply]
  unfold relModularUnitary relConnesCocycle
  calc
    E_ψ.unitary t * X * E_φ.unitary (-t)
        = E_ψ.unitary t * X * (E_ψ.unitary (-t) * E_ψ.unitary t) * E_φ.unitary (-t) := by
      rw [E_ψ.unitary_neg_mul, Matrix.mul_one]
    _ = (E_ψ.unitary t * X * E_ψ.unitary (-t)) * (E_ψ.unitary t * E_φ.unitary (-t)) := by
      simp only [Matrix.mul_assoc]

/-- Commutation of `Δ_{ψ,φ}^{it}` with `Δ_{ψ,φ}`. -/
theorem relModularUnitary_comm_relModularOp (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularUnitary E_ψ E_φ t
        (relModularOp E_ψ.toPositiveComplexDensityFactor E_φ.toPositiveComplexDensityFactor X) =
      relModularOp E_ψ.toPositiveComplexDensityFactor E_φ.toPositiveComplexDensityFactor
        (relModularUnitary E_ψ E_φ t X) := by
  unfold relModularUnitary relModularOp
  rw [E_ψ.toPositiveComplexDensityFactor_rho, E_φ.toPositiveComplexDensityFactor_rhoInv]
  calc
    E_ψ.unitary t * (E_ψ.rho * X * E_φ.rhoInv) * E_φ.unitary (-t)
        = (E_ψ.unitary t * E_ψ.rho) * X * (E_φ.rhoInv * E_φ.unitary (-t)) := by
      simp only [Matrix.mul_assoc]
    _ = (E_ψ.rho * E_ψ.unitary t) * X * (E_φ.unitary (-t) * E_φ.rhoInv) := by
      rw [(E_ψ.rho_commute_unitary t).eq, (E_φ.rhoInv_commute_unitary (-t)).eq]
    _ = E_ψ.rho * (E_ψ.unitary t * X * E_φ.unitary (-t)) * E_φ.rhoInv := by
      simp only [Matrix.mul_assoc]

end ConnesCocycleBridge

/-! =========================================================================
    3. Explicit Noncommuting `2 × 2` Witness (OpenGauss T16 / T17)
    ========================================================================= -/

section NoncommutingWitness

/-- Rational orthonormal rotation `U ∈ M₂(ℂ)` with entries `3/5, ±4/5`. -/
def witnessRotationU : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(3 / 5 : ℂ), (4 / 5 : ℂ); -(4 / 5 : ℂ), (3 / 5 : ℂ)]

private lemma witnessRotationU_conjTranspose :
    witnessRotationUᴴ = !![(3 / 5 : ℂ), -(4 / 5 : ℂ); (4 / 5 : ℂ), (3 / 5 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessRotationU, Matrix.conjTranspose_apply]

theorem witnessRotationU_mul_conjTranspose :
    witnessRotationU * witnessRotationUᴴ = 1 := by
  rw [witnessRotationU_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessRotationU, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

theorem witnessRotationU_conjTranspose_mul :
    witnessRotationUᴴ * witnessRotationU = 1 := by
  rw [witnessRotationU_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessRotationU, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

/-- Unit element packaging `witnessRotationU` and its inverse `witnessRotationUᴴ`. -/
def witnessRotationUUnit : (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := witnessRotationU
  inv := witnessRotationUᴴ
  val_inv := witnessRotationU_mul_conjTranspose
  inv_val := witnessRotationU_conjTranspose_mul

/-- Diagonal Hermitian generator `H_φ = diag(1, -1)`. -/
def witnessHPhi : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 : ℂ), (-1 : ℂ)]

/-- Rotated Hermitian generator `H_ψ = U diag(1, -1) Uᴴ`. -/
def witnessHPsi : Matrix (Fin 2) (Fin 2) ℂ :=
  witnessRotationU * witnessHPhi * witnessRotationUᴴ

theorem witnessHPhi_isHermitian : witnessHPhi.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessHPhi]

theorem witnessHPsi_isHermitian : witnessHPsi.IsHermitian := by
  unfold witnessHPsi
  change (witnessRotationU * witnessHPhi * witnessRotationUᴴ)ᴴ =
    witnessRotationU * witnessHPhi * witnessRotationUᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    witnessHPhi_isHermitian.eq, Matrix.mul_assoc]

/-- Concrete exponential density factor for `φ`. -/
def witnessExpPhi : ExpDensityFactor 2 where
  H := witnessHPhi
  H_herm := witnessHPhi_isHermitian

/-- Concrete exponential density factor for `ψ`. -/
def witnessExpPsi : ExpDensityFactor 2 where
  H := witnessHPsi
  H_herm := witnessHPsi_isHermitian

/-- Nullary density matrix `ρ_φ = witnessExpPhi.rho`. -/
def witnessRhoPhi : Matrix (Fin 2) (Fin 2) ℂ :=
  witnessExpPhi.rho

/-- Nullary density matrix `ρ_ψ = witnessExpPsi.rho`. -/
def witnessRhoPsi : Matrix (Fin 2) (Fin 2) ℂ :=
  witnessExpPsi.rho

theorem witnessRhoPhi_eq :
    witnessRhoPhi = Matrix.diagonal ![Complex.exp (1 : ℂ), Complex.exp (-1 : ℂ)] := by
  unfold witnessRhoPhi ExpDensityFactor.rho witnessExpPhi witnessHPhi
  rw [Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]

theorem witnessRhoPsi_eq :
    witnessRhoPsi = witnessRotationU * witnessRhoPhi * witnessRotationUᴴ := by
  unfold witnessRhoPsi witnessRhoPhi ExpDensityFactor.rho witnessExpPsi witnessExpPhi witnessHPsi
  have hconj := Matrix.exp_units_conj witnessRotationUUnit witnessHPhi
  simpa [witnessRotationUUnit, Matrix.mul_assoc] using hconj

private lemma exp_one_ne_exp_neg_one_complex :
    Complex.exp (1 : ℂ) ≠ Complex.exp (-1 : ℂ) := by
  intro h
  have hreal : (Real.exp 1 : ℂ) = (Real.exp (-1) : ℂ) := by
    simpa only [Complex.ofReal_exp, Complex.ofReal_one, Complex.ofReal_neg] using h
  have hre : Real.exp 1 = Real.exp (-1) := Complex.ofReal_injective hreal
  have hlt : Real.exp (-1) < Real.exp 1 := Real.exp_strictMono (by norm_num)
  exact (ne_of_lt hlt) hre.symm

/-- Explicit noncommutativity witness for the densities: `ρ_ψ * ρ_φ ≠ ρ_φ * ρ_ψ`. -/
theorem witnessRhoPsi_mul_witnessRhoPhi_ne :
    witnessRhoPsi * witnessRhoPhi ≠ witnessRhoPhi * witnessRhoPsi := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  rw [witnessRhoPsi_eq, witnessRhoPhi_eq] at h01
  have hL :
      ((witnessRotationU * Matrix.diagonal ![Complex.exp (1 : ℂ), Complex.exp (-1 : ℂ)] *
        witnessRotationUᴴ) * Matrix.diagonal ![Complex.exp (1 : ℂ), Complex.exp (-1 : ℂ)]) 0 1 =
        (12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ)) * Complex.exp (-1 : ℂ) := by
    rw [witnessRotationU_conjTranspose]
    simp [witnessRotationU, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  have hR :
      (Matrix.diagonal ![Complex.exp (1 : ℂ), Complex.exp (-1 : ℂ)] *
        (witnessRotationU * Matrix.diagonal ![Complex.exp (1 : ℂ), Complex.exp (-1 : ℂ)] *
          witnessRotationUᴴ)) 0 1 =
        Complex.exp (1 : ℂ) * ((12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ))) := by
    rw [witnessRotationU_conjTranspose]
    simp [witnessRotationU, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [hL, hR] at h01
  have hdiff_sq :
      (12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ)) ^ 2 = 0 := by
    have hsub :
        (12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ)) * Complex.exp (-1 : ℂ) -
          Complex.exp (1 : ℂ) *
            ((12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ))) = 0 :=
      sub_eq_zero.mpr h01
    have hfactor :
        (12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ)) ^ 2 =
          (12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ)) * Complex.exp (-1 : ℂ) -
            Complex.exp (1 : ℂ) *
              ((12 / 25 : ℂ) * (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ))) := by
      ring
    exact hfactor.trans hsub
  have hc : (12 / 25 : ℂ) ≠ 0 := by norm_num
  have hsq : (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ)) ^ 2 = 0 :=
    (mul_eq_zero.mp hdiff_sq).resolve_left hc
  have hdiff : Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ) = 0 := sq_eq_zero_iff.mp hsq
  exact exp_one_ne_exp_neg_one_complex (sub_eq_zero.mp hdiff).symm

/-- Nonvanishing commutator `[ρ_ψ, ρ_φ] = ρ_ψ ρ_φ - ρ_φ ρ_ψ ≠ 0`. -/
theorem witnessRhoPsi_commutator_ne_zero :
    witnessRhoPsi * witnessRhoPhi - witnessRhoPhi * witnessRhoPsi ≠ 0 :=
  sub_ne_zero.mpr witnessRhoPsi_mul_witnessRhoPhi_ne

theorem witnessExpPhi_unitary_pi_div_two :
    witnessExpPhi.unitary (Real.pi / 2) = Matrix.diagonal ![Complex.I, -Complex.I] := by
  unfold ExpDensityFactor.unitary witnessExpPhi witnessHPhi
  have hsmul :
      (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • Matrix.diagonal ![(1 : ℂ), (-1 : ℂ)] =
        Matrix.diagonal ![(Real.pi / 2 : ℂ) * Complex.I, -(Real.pi : ℂ) / 2 * Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [mul_comm]; try ring)
  rw [hsmul, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_pi_div_two_mul_I,
      Complex.exp_neg_pi_div_two_mul_I]

theorem witnessExpPhi_unitary_neg_pi_div_two :
    witnessExpPhi.unitary (-(Real.pi / 2)) = Matrix.diagonal ![-Complex.I, Complex.I] := by
  rw [← witnessExpPhi.unitary_conjTranspose (Real.pi / 2), witnessExpPhi_unitary_pi_div_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem witnessExpPsi_unitary_pi_div_two :
    witnessExpPsi.unitary (Real.pi / 2) =
      witnessRotationU * Matrix.diagonal ![Complex.I, -Complex.I] * witnessRotationUᴴ := by
  unfold ExpDensityFactor.unitary witnessExpPsi witnessHPsi
  have hsmul :
      (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
          (witnessRotationU * witnessHPhi * witnessRotationUᴴ) =
        witnessRotationU * ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • witnessHPhi) *
          witnessRotationUᴴ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hsmul]
  have hconj :=
    Matrix.exp_units_conj witnessRotationUUnit ((Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • witnessHPhi)
  have hphi := witnessExpPhi_unitary_pi_div_two
  unfold ExpDensityFactor.unitary witnessExpPhi at hphi
  rw [hphi] at hconj
  simpa [witnessRotationUUnit, Matrix.mul_assoc] using hconj

/-- Explicit off-diagonal entry of the Connes cocycle at `t = π / 2`: `(u_{π/2})_{0,1} = 24/25`. -/
theorem witnessCocycle_at_pi_div_two_01 :
    relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2) 0 1 = (24 / 25 : ℂ) := by
  unfold relConnesCocycle
  rw [witnessExpPsi_unitary_pi_div_two, witnessExpPhi_unitary_neg_pi_div_two,
    witnessRotationU_conjTranspose]
  simp [witnessRotationU, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- The Connes cocycle `u_{π/2}` is genuinely non-scalar (rules out `c • 1` surrogates). -/
theorem witnessCocycle_nonscalar :
    ∀ c : ℂ,
      relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2) ≠
        c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro c h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  rw [witnessCocycle_at_pi_div_two_01] at h01
  norm_num at h01

/-- The Connes cocycle `u_{π/2}` fails to commute with the diagonal projection `diag(1, 0)`. -/
theorem witnessCocycle_noncomm_diag :
    let u := relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2)
    let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1 : ℂ), (0 : ℂ)]
    u * P ≠ P * u := by
  intro u P h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have hL : (u * P) 0 1 = 0 := by
    simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : (P * u) 0 1 = (24 / 25 : ℂ) := by
    have hu01 : u 0 1 = (24 / 25 : ℂ) := witnessCocycle_at_pi_div_two_01
    simp [P, Matrix.mul_apply, Fin.sum_univ_two, hu01]
  rw [hL, hR] at h01
  norm_num at h01

end NoncommutingWitness

end InfoGeometry.Modular.ComplexRelativeModularRN

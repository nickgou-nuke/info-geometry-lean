/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Modular.TomitaCommutantDuality
import InfoGeometry.Modular.TomitaChiralJ

/-!
# Complex Finite-Matrix Tomita–Takesaki Commutant Duality & Polar Decomposition (`F2a`)

This module constructs the genuine complex finite-dimensional Tomita–Takesaki
commutant duality and polar decomposition on `Matrix (Fin n) (Fin n) ℂ`
(distinct from the real matrix carrier in `FiniteMatrixTomitaPolar.lean`).

Main results proved unconditionally without external inclusions:
1. `matrixJ n : AntiLinearInvolution (Matrix (Fin n) (Fin n) ℂ)` via conjugate
   transpose `X ↦ Xᴴ`, preserving the complex Hilbert–Schmidt pairing
   `hsInner X Y = (Xᴴ * Y).trace` up to complex conjugation (`hsInner_matrixJ`).
2. `leftReg_commutant_eq_rightReg`: for the **full** left regular representation
   `leftRegSet n = { leftMul A | A }` and **full** right regular representation
   `rightRegSet n = { rightMul B | B }`, `commutant (leftRegSet n) = rightRegSet n`,
   proved directly by evaluating any commuting operator on `1`.
3. `complexMatrixTomitaDualityData`: genuine inhabitant of
   `TomitaCommutantDuality.TomitaDualityData (matrixJ n) (leftRegSet n)`, giving
   unconditionally `J (L(M_n)) J = (L(M_n))'` and `(L(M_n))'' = L(M_n)`.
4. `PositiveComplexDensityFactor n` and `complexMatrixTomitaModularData`: constructs
   `S(X) = r⁻¹ Xᴴ r`, `Δ(X) = ρ X ρ⁻¹`, `Δ^{1/2}(X) = r X r⁻¹`, proving `S = J Δ^{1/2}`,
   `J Δ J = Δ⁻¹`, complex KMS cyclicity `state F (A * modularOp F B) = state F (B * A)`,
   and inhabiting `TomitaChiralJ.TomitaModularData`.
5. `mat2_complex_noncomm_witness`: closed OpenGauss T16 noncommutativity witness
   on `Matrix (Fin 2) (Fin 2) ℂ`.
-/

noncomputable section

namespace InfoGeometry.Modular.ComplexMatrixTomitaDuality

open Matrix Complex
open InfoGeometry.Modular.TomitaCommutantDuality
open InfoGeometry.Modular.TomitaChiralJ

/-! =========================================================================
    1. OpenGauss T16 Noncommutativity Witness on M₂(ℂ)
    ========================================================================= -/

/-- Explicit noncommuting `2 × 2` complex matrix witness (`E₀₁ * E₁₀ ≠ E₁₀ * E₀₁`). -/
theorem mat2_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  let E01 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 1], ![0, 0]]
  let E10 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 0], ![1, 0]]
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  have hL : (E01 * E10) 0 0 = 1 := by
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : (E10 * E01) 0 0 = 0 := by
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hL, hR] at h00
  exact one_ne_zero h00

/-! =========================================================================
    2. Complex Hilbert–Schmidt Inner Product & Anti-Linear Involution J
    ========================================================================= -/

section Duality

variable (n : ℕ)

/-- Complex Hilbert–Schmidt inner product `⟨X, Y⟩_HS = Tr(Xᴴ Y)`. -/
def hsInner (X Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (Xᴴ * Y).trace

theorem hsInner_conj_symm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    star (hsInner n X Y) = hsInner n Y X := by
  unfold hsInner
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Anti-linear modular conjugation `J(X) = Xᴴ` on `M_n(ℂ)`. -/
def matrixJ : AntiLinearInvolution (Matrix (Fin n) (Fin n) ℂ) where
  toFun := fun X => Xᴴ
  map_add' := Matrix.conjTranspose_add
  map_smul' := fun c X => Matrix.conjTranspose_smul c X
  involutive' := Matrix.conjTranspose_conjTranspose

@[simp]
theorem matrixJ_apply (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixJ n X = Xᴴ := rfl

/-- `J` is anti-unitary for the complex Hilbert–Schmidt pairing:
`⟨J X, J Y⟩_HS = ⟨Y, X⟩_HS`. -/
theorem hsInner_matrixJ (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n (matrixJ n X) (matrixJ n Y) = hsInner n Y X := by
  unfold hsInner
  rw [matrixJ_apply, matrixJ_apply, Matrix.conjTranspose_conjTranspose]
  exact Matrix.trace_mul_comm X Yᴴ

/-! =========================================================================
    3. Full Left and Right Regular Representations & Commutant Theorem
    ========================================================================= -/

/-- Left regular multiplication operator `L_A(X) = A * X`. -/
def leftMul (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  fun X => A * X

/-- Right regular multiplication operator `R_B(X) = X * B`. -/
def rightMul (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
  fun X => X * B

/-- The full left regular representation of `M_n(ℂ)`. -/
def leftRegSet : Set (Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  { T | ∃ A, T = leftMul n A }

/-- The full right regular representation of `M_n(ℂ)`. -/
def rightRegSet : Set (Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  { T | ∃ B, T = rightMul n B }

/-- Associativity commutant identity: `R_B (L_A X) = L_A (R_B X)`. -/
theorem rightMul_comm_leftMul (A B X : Matrix (Fin n) (Fin n) ℂ) :
    rightMul n B (leftMul n A X) = leftMul n A (rightMul n B X) := by
  unfold leftMul rightMul
  exact Matrix.mul_assoc A X B

/-- Unconditional commutant theorem for the full left regular representation:
`{L_A | A ∈ M_n(ℂ)}' = {R_B | B ∈ M_n(ℂ)}`. -/
theorem leftReg_commutant_eq_rightReg :
    commutant (leftRegSet n) = rightRegSet n := by
  ext T
  constructor
  · intro hT
    refine ⟨T 1, ?_⟩
    funext X
    have hX := hT (leftMul n X) ⟨X, rfl⟩ 1
    calc
      T X = T (leftMul n X 1) := by simp [leftMul]
      _ = leftMul n X (T 1) := hX
      _ = rightMul n (T 1) X := rfl
  · rintro ⟨B, rfl⟩ A ⟨a, rfl⟩ X
    exact rightMul_comm_leftMul n a B X

/-- Unconditional commutant theorem for the full right regular representation:
`{R_B | B ∈ M_n(ℂ)}' = {L_A | A ∈ M_n(ℂ)}`. -/
theorem rightReg_commutant_eq_leftReg :
    commutant (rightRegSet n) = leftRegSet n := by
  ext T
  constructor
  · intro hT
    refine ⟨T 1, ?_⟩
    funext X
    have hX := hT (rightMul n X) ⟨X, rfl⟩ 1
    calc
      T X = T (rightMul n X 1) := by simp [rightMul]
      _ = rightMul n X (T 1) := hX
      _ = leftMul n (T 1) X := rfl
  · rintro ⟨A, rfl⟩ B ⟨b, rfl⟩ X
    exact (rightMul_comm_leftMul n A b X).symm

/-- Spatial conjugation identity `J ∘ L_A ∘ J = R_{Aᴴ}`. -/
theorem AdJ_leftMul_eq_rightMul_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) :
    AdJ (matrixJ n) (leftMul n A) = rightMul n Aᴴ := by
  funext X
  dsimp [AdJ, leftMul, rightMul, matrixJ]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Spatial conjugation identity `J ∘ R_B ∘ J = L_{Bᴴ}`. -/
theorem AdJ_rightMul_eq_leftMul_conjTranspose (B : Matrix (Fin n) (Fin n) ℂ) :
    AdJ (matrixJ n) (rightMul n B) = leftMul n Bᴴ := by
  funext X
  dsimp [AdJ, leftMul, rightMul, matrixJ]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Genuine unconditional inhabitant of `TomitaDualityData (matrixJ n) (leftRegSet n)`. -/
theorem complexMatrixTomitaDualityData :
    TomitaDualityData (matrixJ n) (leftRegSet n) where
  forward_commute := by
    rintro _ ⟨A, rfl⟩
    rw [AdJ_leftMul_eq_rightMul_conjTranspose, leftReg_commutant_eq_rightReg]
    exact ⟨Aᴴ, rfl⟩
  backward_span := by
    intro T hT
    rw [leftReg_commutant_eq_rightReg] at hT
    rcases hT with ⟨B, rfl⟩
    refine ⟨leftMul n Bᴴ, ⟨Bᴴ, rfl⟩, ?_⟩
    rw [AdJ_leftMul_eq_rightMul_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- Genuine unconditional inhabitant of `TomitaDualityData (matrixJ n) (rightRegSet n)`. -/
theorem complexMatrixTomitaDualityData_right :
    TomitaDualityData (matrixJ n) (rightRegSet n) where
  forward_commute := by
    rintro _ ⟨B, rfl⟩
    rw [AdJ_rightMul_eq_leftMul_conjTranspose, rightReg_commutant_eq_leftReg]
    exact ⟨Bᴴ, rfl⟩
  backward_span := by
    intro T hT
    rw [rightReg_commutant_eq_leftReg] at hT
    rcases hT with ⟨A, rfl⟩
    refine ⟨rightMul n Aᴴ, ⟨Aᴴ, rfl⟩, ?_⟩
    rw [AdJ_rightMul_eq_leftMul_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- Unconditional complex matrix Tomita–Takesaki theorem: `L(M_n)' = J L(M_n) J`. -/
theorem complexMatrix_commutant_eq_JConjugate :
    commutant (leftRegSet n) = JConjugateSet (matrixJ n) (leftRegSet n) :=
  tomita_takesaki_commutant_duality (complexMatrixTomitaDualityData n)

/-- Unconditional complex matrix von Neumann bicommutant theorem: `L(M_n)'' = L(M_n)`. -/
theorem complexMatrix_bicommutant_eq_self :
    commutant (commutant (leftRegSet n)) = leftRegSet n :=
  von_neumann_bicommutant_from_tomita (complexMatrixTomitaDualityData n)
    (by
      rw [leftReg_commutant_eq_rightReg]
      exact complexMatrixTomitaDualityData_right n)

end Duality

/-! =========================================================================
    4. Complex Density Polar Decomposition S = J Δ^{1/2} and KMS Identity
    ========================================================================= -/

section Polar

variable {n : ℕ}

/-- Invertible Hermitian square-root density factor `r = ρ^{1/2}` on `M_n(ℂ)`. -/
structure PositiveComplexDensityFactor (n : ℕ) where
  r : Matrix (Fin n) (Fin n) ℂ
  rInv : Matrix (Fin n) (Fin n) ℂ
  r_herm : rᴴ = r
  rInv_herm : rInvᴴ = rInv
  r_mul_rInv : r * rInv = 1
  rInv_mul_r : rInv * r = 1

namespace PositiveComplexDensityFactor

def rho (F : PositiveComplexDensityFactor n) : Matrix (Fin n) (Fin n) ℂ :=
  F.r * F.r

def rhoInv (F : PositiveComplexDensityFactor n) : Matrix (Fin n) (Fin n) ℂ :=
  F.rInv * F.rInv

theorem rho_herm (F : PositiveComplexDensityFactor n) : F.rhoᴴ = F.rho := by
  unfold rho
  rw [Matrix.conjTranspose_mul, F.r_herm]

theorem rhoInv_herm (F : PositiveComplexDensityFactor n) : F.rhoInvᴴ = F.rhoInv := by
  unfold rhoInv
  rw [Matrix.conjTranspose_mul, F.rInv_herm]

theorem rho_mul_rhoInv (F : PositiveComplexDensityFactor n) : F.rho * F.rhoInv = 1 := by
  unfold rho rhoInv
  calc
    F.r * F.r * (F.rInv * F.rInv) = F.r * (F.r * F.rInv) * F.rInv := by
      simp only [Matrix.mul_assoc]
    _ = F.r * 1 * F.rInv := by rw [F.r_mul_rInv]
    _ = 1 := by simp [F.r_mul_rInv]

theorem rhoInv_mul_rho (F : PositiveComplexDensityFactor n) : F.rhoInv * F.rho = 1 := by
  unfold rho rhoInv
  calc
    F.rInv * F.rInv * (F.r * F.r) = F.rInv * (F.rInv * F.r) * F.r := by
      simp only [Matrix.mul_assoc]
    _ = F.rInv * 1 * F.r := by rw [F.rInv_mul_r]
    _ = 1 := by simp [F.rInv_mul_r]

end PositiveComplexDensityFactor

/-- Complex matrix density trace state `ω_ρ(X) = Tr(ρ X)`. -/
def state (F : PositiveComplexDensityFactor n) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (F.rho * X).trace

/-- Cyclic vector identity `ω_ρ(X) = ⟨r, X r⟩_HS` with cyclic vector `Ω = r`. -/
theorem state_eq_hsInner_cyclic (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    state F X = hsInner n F.r (X * F.r) := by
  unfold state PositiveComplexDensityFactor.rho hsInner
  rw [F.r_herm, Matrix.mul_assoc, Matrix.trace_mul_comm F.r (F.r * X)]
  simp only [Matrix.mul_assoc]

/-- Complex Tomita operator `S(X) = r⁻¹ Xᴴ r` on GNS coordinates. -/
def tomitaOp (F : PositiveComplexDensityFactor n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  F.rInv * Xᴴ * F.r

theorem tomitaOp_on_cyclic (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    tomitaOp F (X * F.r) = Xᴴ * F.r := by
  unfold tomitaOp
  rw [Matrix.conjTranspose_mul, F.r_herm]
  calc
    F.rInv * (F.r * Xᴴ) * F.r = (F.rInv * F.r) * Xᴴ * F.r := by
      simp only [Matrix.mul_assoc]
    _ = Xᴴ * F.r := by rw [F.rInv_mul_r, Matrix.one_mul]

theorem tomitaOp_add (F : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    tomitaOp F (X + Y) = tomitaOp F X + tomitaOp F Y := by
  unfold tomitaOp
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem tomitaOp_smul (F : PositiveComplexDensityFactor n)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    tomitaOp F (c • X) = star c • tomitaOp F X := by
  unfold tomitaOp
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem tomitaOp_involution (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    tomitaOp F (tomitaOp F X) = X := by
  unfold tomitaOp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    F.r_herm, F.rInv_herm]
  calc
    F.rInv * (F.r * (X * F.rInv)) * F.r = (F.rInv * F.r) * X * (F.rInv * F.r) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [F.rInv_mul_r, Matrix.one_mul, Matrix.mul_one]

theorem tomitaOp_cyclic (F : PositiveComplexDensityFactor n) :
    tomitaOp F F.r = F.r := by
  unfold tomitaOp
  rw [F.r_herm, F.rInv_mul_r, Matrix.one_mul]

/-- Hilbert–Schmidt adjoint `F(X) = r Xᴴ r⁻¹` of `S`. -/
def tomitaAdjOp (F : PositiveComplexDensityFactor n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  F.r * Xᴴ * F.rInv

/-- Complex anti-linear adjoint relation `⟨X, S Y⟩_HS = ⟨Y, F X⟩_HS`. -/
theorem hsInner_tomitaOp_eq (F : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n X (tomitaOp F Y) = hsInner n Y (tomitaAdjOp F X) := by
  unfold hsInner tomitaOp tomitaAdjOp
  calc
    (Xᴴ * (F.rInv * Yᴴ * F.r)).trace = ((Xᴴ * F.rInv) * (Yᴴ * F.r)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((Yᴴ * F.r) * (Xᴴ * F.rInv)).trace := Matrix.trace_mul_comm _ _
    _ = (Yᴴ * (F.r * Xᴴ * F.rInv)).trace := by simp only [Matrix.mul_assoc]

/-- Modular operator `Δ(X) = ρ X ρ⁻¹`. -/
def modularOp (F : PositiveComplexDensityFactor n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  F.rho * X * F.rhoInv

/-- Inverse modular operator `Δ⁻¹(X) = ρ⁻¹ X ρ`. -/
def modularInvOp (F : PositiveComplexDensityFactor n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  F.rhoInv * X * F.rho

/-- Square root of modular operator `Δ^{1/2}(X) = r X r⁻¹`. -/
def modularSqrt (F : PositiveComplexDensityFactor n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  F.r * X * F.rInv

/-- Inverse square root `Δ^{-1/2}(X) = r⁻¹ X r`. -/
def modularInvSqrt (F : PositiveComplexDensityFactor n) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  F.rInv * X * F.r

/-- `F ∘ S = Δ` on `M_n(ℂ)`. -/
theorem modularOp_eq_adj_comp_tomita (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    tomitaAdjOp F (tomitaOp F X) = modularOp F X := by
  unfold tomitaAdjOp tomitaOp modularOp
    PositiveComplexDensityFactor.rho PositiveComplexDensityFactor.rhoInv
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    F.r_herm, F.rInv_herm]
  simp only [Matrix.mul_assoc]

/-- Polar decomposition `S = J ∘ Δ^{1/2}` on `M_n(ℂ)`. -/
theorem tomita_polar_decomposition (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    tomitaOp F X = matrixJ n (modularSqrt F X) := by
  unfold tomitaOp modularSqrt
  rw [matrixJ_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    F.r_herm, F.rInv_herm, Matrix.mul_assoc]

/-- `J Δ J = Δ⁻¹` on `M_n(ℂ)`. -/
theorem matrixJ_modularOp_conj (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixJ n (modularOp F (matrixJ n X)) = modularInvOp F X := by
  unfold modularOp modularInvOp
  rw [matrixJ_apply, matrixJ_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, F.rho_herm, F.rhoInv_herm, Matrix.mul_assoc]

/-- Modular operator self-adjointness `⟨X, Δ Y⟩_HS = ⟨Δ X, Y⟩_HS`. -/
theorem modularOp_hsSelfAdjoint (F : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    hsInner n X (modularOp F Y) = hsInner n (modularOp F X) Y := by
  unfold hsInner modularOp
  have hL :
      (Xᴴ * (F.rho * Y * F.rhoInv)).trace =
        (F.rhoInv * Xᴴ * F.rho * Y).trace := by
    calc
      (Xᴴ * (F.rho * Y * F.rhoInv)).trace = ((Xᴴ * F.rho * Y) * F.rhoInv).trace := by
        simp only [Matrix.mul_assoc]
      _ = (F.rhoInv * (Xᴴ * F.rho * Y)).trace := Matrix.trace_mul_comm _ _
      _ = (F.rhoInv * Xᴴ * F.rho * Y).trace := by simp only [Matrix.mul_assoc]
  have hR :
      ((F.rho * X * F.rhoInv)ᴴ * Y).trace =
        (F.rhoInv * Xᴴ * F.rho * Y).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, F.rho_herm, F.rhoInv_herm]
    simp only [Matrix.mul_assoc]
  exact hL.trans hR.symm

/-- Exact complex matrix KMS cyclicity: `ω_ρ(A Δ(B)) = ω_ρ(B A)`. -/
theorem modularOp_kms_identity (F : PositiveComplexDensityFactor n)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    state F (A * modularOp F B) = state F (B * A) := by
  unfold state modularOp
  calc
    (F.rho * (A * (F.rho * B * F.rhoInv))).trace
        = ((F.rho * A * F.rho * B) * F.rhoInv).trace := by
      simp only [Matrix.mul_assoc]
    _ = (F.rhoInv * (F.rho * A * F.rho * B)).trace := Matrix.trace_mul_comm _ _
    _ = ((F.rhoInv * F.rho) * A * F.rho * B).trace := by
      simp only [Matrix.mul_assoc]
    _ = (A * (F.rho * B)).trace := by
      rw [F.rhoInv_mul_rho, Matrix.one_mul, Matrix.mul_assoc]
    _ = (F.rho * (B * A)).trace := by
      rw [Matrix.trace_mul_comm A (F.rho * B), Matrix.mul_assoc]

/-- Complex linear map bundling `Δ^{1/2}(X) = r X r⁻¹`. -/
def modularSqrtLinear (F : PositiveComplexDensityFactor n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := modularSqrt F
  map_add' := fun X Y => by
    unfold modularSqrt
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun c X => by
    unfold modularSqrt
    rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- Complex linear map bundling `Δ^{-1/2}(X) = r⁻¹ X r`. -/
def modularInvSqrtLinear (F : PositiveComplexDensityFactor n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := modularInvSqrt F
  map_add' := fun X Y => by
    unfold modularInvSqrt
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun c X => by
    unfold modularInvSqrt
    rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- Genuine inhabitant of `TomitaChiralJ.TomitaModularData` on `M_n(ℂ)` for any
invertible Hermitian density factor `F`. -/
def complexMatrixTomitaModularData (F : PositiveComplexDensityFactor n) :
    TomitaModularData (Matrix (Fin n) (Fin n) ℂ) where
  vacuum := F.r
  S₀ := tomitaOp F
  S₀_add := tomitaOp_add F
  S₀_smul := tomitaOp_smul F
  S₀_involutive := tomitaOp_involution F
  S₀_vacuum := tomitaOp_cyclic F
  delta_half := modularSqrtLinear F
  delta_inv_half := modularInvSqrtLinear F
  delta_half_inv := fun X => by
    change F.r * (F.rInv * X * F.r) * F.rInv = X
    calc
      F.r * (F.rInv * X * F.r) * F.rInv = (F.r * F.rInv) * X * (F.r * F.rInv) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [F.r_mul_rInv, Matrix.one_mul, Matrix.mul_one]
  delta_inv_half_right := fun X => by
    change F.rInv * (F.r * X * F.rInv) * F.r = X
    calc
      F.rInv * (F.r * X * F.rInv) * F.r = (F.rInv * F.r) * X * (F.rInv * F.r) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [F.rInv_mul_r, Matrix.one_mul, Matrix.mul_one]
  delta_vacuum := by
    change F.r * F.r * F.rInv = F.r
    rw [Matrix.mul_assoc, F.r_mul_rInv, Matrix.mul_one]
  delta_inv_vacuum := by
    change F.rInv * F.r * F.r = F.r
    rw [F.rInv_mul_r, Matrix.one_mul]

/-- The constructed `TomitaChiralJ.modularJ` on `complexMatrixTomitaModularData F` equals `matrixJ n`. -/
theorem modularJ_complexMatrix_eq (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    TomitaChiralJ.modularJ (complexMatrixTomitaModularData F) X = matrixJ n X := by
  dsimp [TomitaChiralJ.modularJ, complexMatrixTomitaModularData, tomitaOp, modularInvSqrtLinear,
    modularInvSqrt, matrixJ]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, F.r_herm, F.rInv_herm]
  calc
    F.rInv * (F.r * (Xᴴ * F.rInv)) * F.r = (F.rInv * F.r) * Xᴴ * (F.rInv * F.r) := by
      simp only [Matrix.mul_assoc]
    _ = Xᴴ := by rw [F.rInv_mul_r, Matrix.one_mul, Matrix.mul_one]

end Polar

end InfoGeometry.Modular.ComplexMatrixTomitaDuality

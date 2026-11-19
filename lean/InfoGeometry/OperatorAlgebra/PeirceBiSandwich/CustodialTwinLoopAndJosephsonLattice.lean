/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Core
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.PinchedSuperExtension
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Clifford8BdGHorizon
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Supertwistor16AndRealBloch
import InfoGeometry.OperatorAlgebra.PeirceSpine.CustodialTwinExchangeProtection
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Custodial Twin Involution, All-Loop Protection, Birefringence & Josephson Lattice

Formalizes Archetype 3 (`Poset U₀ ≺ … ≺ U₉`) of the Peirce bi-sandwich operator algebra:
1. `ℤ₂` real freeze in `M₈(ℝ)`:
   - `D1_8_Z = (-j) * J_spin` is symmetric (`D1_8_Zᵀ = D1_8_Z`).
   - `D2_8_Z = (-Φ) * J_spin` is skew-symmetric (`D2_8_Zᵀ = -D2_8_Z`).
   - In `M₈(ℝ)`, the Cartan charge `Σ` is symmetric and cannot generate unitary rotations.
2. `U(1)` BdG circle in `Mat16Prod := M₈(ℝ) ⊗ M₂(ℝ)_phase`:
   - Adjoining `J_phase2` unlocks the skew-adjoint charge generator `G_U1_16 = Σ ⊗ J_phase2`.
   - `comm G_U1_16 D1_16 = 2 • D2_16`.
   - Continuous condensate circle `Delta_U1(θ) = cos(θ) • D1_16 + sin(θ) • D2_16`.
   - Exact BdG dispersion gap `Delta_U1(θ) * Delta_U1(θ) = V16` for all `θ : ℝ`.
3. Custodial twin involution `W_twin = Φ + P₀`:
   - `W_twin_Z * W_twin_Z = 1`, `W_twin_Zᵀ = W_twin_Z`.
   - Commutes with horizon `[W_twin_Z, H_hor_Z] = 0` and fixes `P₀`.
   - Conjugates `D1_8_Z` to `-D1_8_Z` (`W_twin_Z * D1_8_Z * W_twin_Z = -D1_8_Z`).
   - All-loop polynomial odd-power vanishing on `P₀`:
     `P0_8_R * F(H_hor) * D1_8_R^(2m+1) * G(H_hor) * P0_8_R = 0` for all `F, G ∈ ℝ[X]`.
   - Lifted `W_twin16 = W_twin_Z ⊗ I₂` and Lorentz boost commutation for even powers
     `K8_16 * (D1_16 ^ (2 * m)) - (D1_16 ^ (2 * m)) * K8_16 = 0`.
4. 1-loop parity-odd birefringence:
   - `P0_16 * H16 * Delta_U1(θ) * H16 * P0_16 = (2 * sin(θ)) • M_biref`,
     with explicit non-zero matrix `M_biref = ((P₀ + G₈) J_spin) ⊗ J_phase2`.
5. Josephson cosine coupling and sub-isometric off-shell defect:
   - Condensate overlap trace `(Delta_U1(θx) * Delta_U1(θy)).trace = 8 * cos(θx - θy)`.
   - Sub-isometric deformation `V16_eps(ε) = (1 - ε) • V16` induces the off-shell defect
     `casimirDefect(V16_eps(ε)) = (-ε * (1 - ε)) • V16`.
6. OpenGauss T16 non-commutativity witness on `Mat16Prod`.
-/

noncomputable section

open scoped Kronecker

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

/-! ### Helper Lemmas for Kronecker Products and Commutators -/

lemma I2_R_mul (M : Matrix (Fin 2) (Fin 2) ℝ) : I2_R * M = M := by
  dsimp [I2_R]; rw [one_mul]

lemma mul_I2_R (M : Matrix (Fin 2) (Fin 2) ℝ) : M * I2_R = M := by
  dsimp [I2_R]; rw [mul_one]

lemma I2_R_mul_I2_R : I2_R * I2_R = I2_R := by
  dsimp [I2_R]; rw [one_mul]

lemma one_kronecker_I2_R : (1 : Matrix (Fin 8) (Fin 8) ℝ) ⊗ₖ I2_R = 1 := by
  dsimp [I2_R]; rw [Matrix.one_kronecker_one]

lemma sub_kronecker {l m n p : Type*} (A B : Matrix l m ℝ) (C : Matrix n p ℝ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, sub_mul]

lemma kronecker_sub {l m n p : Type*} (A : Matrix l m ℝ) (B C : Matrix n p ℝ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, mul_sub]

lemma neg_kronecker {l m n p : Type*} (A : Matrix l m ℝ) (B : Matrix n p ℝ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.kroneckerMap_apply, neg_mul]

lemma neg_kronecker_neg {l m n p : Type*} (A : Matrix l m ℝ) (B : Matrix n p ℝ) :
    (-A) ⊗ₖ (-B) = A ⊗ₖ B := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.kroneckerMap_apply, mul_neg, neg_mul, neg_neg]

lemma zero_kronecker {l m n p : Type*} (B : Matrix n p ℝ) :
    (0 : Matrix l m ℝ) ⊗ₖ B = 0 := by
  ext i j
  simp only [Matrix.zero_apply, Matrix.kroneckerMap_apply, zero_mul]

lemma kronecker_zero {l m n p : Type*} (A : Matrix l m ℝ) :
    A ⊗ₖ (0 : Matrix n p ℝ) = 0 := by
  ext i j
  simp only [Matrix.zero_apply, Matrix.kroneckerMap_apply, mul_zero]

lemma toMat8R_two_mul (M : Matrix (Fin 8) (Fin 8) ℤ) :
    toMat8R (2 * M) = (2 : ℝ) • toMat8R M := by
  have h_p2 : toMat8R (2 : Matrix (Fin 8) (Fin 8) ℤ) = (2 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [map_ofNat, ← Algebra.algebraMap_eq_smul_one, map_ofNat]
  rw [show (2 * M : Matrix (Fin 8) (Fin 8) ℤ) = (2 : Matrix (Fin 8) (Fin 8) ℤ) * M by rfl,
      map_mul, h_p2, smul_mul_assoc, one_mul]

/-- Central scalars commute with polynomials in any algebra evaluation. -/
lemma aeval_commutes_of_comm {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {W H : A} (h : W * H = H * W) (p : Polynomial R) :
    W * Polynomial.aeval H p = Polynomial.aeval H p * W := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C]
    rw [Algebra.commutes]
  | add p q hp hq =>
    simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial n a ih =>
    have hX : Polynomial.C a * Polynomial.X ^ (n + 1) =
        (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by
      rw [pow_succ, mul_assoc]
    rw [hX, map_mul, Polynomial.aeval_X]
    calc W * (Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * H)
        = (W * Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n)) * H := by rw [mul_assoc]
      _ = (Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * W) * H := by rw [ih]
      _ = Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * (W * H) := by rw [mul_assoc]
      _ = Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * (H * W) := by rw [h]
      _ = (Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * H) * W := by rw [← mul_assoc]

/-! ### Part 1: `ℤ₂` Real Freeze in `M₈(ℝ)` -/

/-- First discrete BdG jump operator in `Mat₈(ℤ)`: `D₁ = (-j) * J_spin`. -/
def D1_8_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  (-jOp P8_Z A8_Z A8_Z) * J8_spin_Z

/-- Second discrete BdG jump operator in `Mat₈(ℤ)`: `D₂ = (-Φ) * J_spin`. -/
def D2_8_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  (-phiOp P8_Z A8_Z A8_Z) * J8_spin_Z

/-- `ℤ₂` real freeze theorem in `M₈(ℤ)`:
    `D₁` is symmetric while `D₂` is skew-symmetric, both squaring to `±V₈` and
    anticommuting, with `comm Σ D₁ = 2 * D₂`. -/
theorem z2_real_freeze_M8 :
    D1_8_Z.transpose = D1_8_Z ∧
    D2_8_Z.transpose = -D2_8_Z ∧
    D1_8_Z * D1_8_Z = casimirV P8_Z A8_Z A8_Z ∧
    D2_8_Z * D2_8_Z = -casimirV P8_Z A8_Z A8_Z ∧
    anticomm D1_8_Z D2_8_Z = 0 ∧
    comm (sigmaOp P8_Z A8_Z A8_Z) D1_8_Z = 2 * D2_8_Z := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ### Part 2: `U(1)` BdG Condensate Circle in `Mat16Prod` -/

/-- Lifted symmetric BdG operator `D₁` in `Mat16Prod := M₈(ℝ) ⊗ M₂(ℝ)_phase`. -/
def D1_16 : Mat16Prod := toMat8R D1_8_Z ⊗ₖ I2_R

/-- Lifted skew-adjoint BdG operator `D₂` in `Mat16Prod`. -/
def D2_16 : Mat16Prod := toMat8R D2_8_Z ⊗ₖ J_phase2

/-- Skew-adjoint continuous `U(1)` phase rotation generator `G_U1 = Σ ⊗ J_phase2`. -/
def G_U1_16 : Mat16Prod := toMat8R (sigmaOp P8_Z A8_Z A8_Z) ⊗ₖ J_phase2

/-- Continuous `U(1)` BdG condensate circle `Delta_U1(θ) = cos(θ) • D₁ + sin(θ) • D₂`. -/
def Delta_U1 (θ : ℝ) : Mat16Prod :=
  Real.cos θ • D1_16 + Real.sin θ • D2_16

lemma d1_16_sq : D1_16 * D1_16 = V16 := by
  dsimp [D1_16, V16]
  rw [← Matrix.mul_kronecker_mul, ← map_mul,
      show D1_8_Z * D1_8_Z = casimirV P8_Z A8_Z A8_Z by decide,
      I2_R_mul_I2_R]

lemma d2_16_sq : D2_16 * D2_16 = V16 := by
  dsimp [D2_16, V16]
  rw [← Matrix.mul_kronecker_mul, J_phase2_sq, ← map_mul,
      show D2_8_Z * D2_8_Z = -casimirV P8_Z A8_Z A8_Z by decide,
      map_neg, neg_kronecker_neg]

lemma anticomm_d1_d2_16 : D1_16 * D2_16 + D2_16 * D1_16 = 0 := by
  dsimp [D1_16, D2_16]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_I2_R, I2_R_mul]
  rw [← Matrix.add_kronecker, ← map_mul, ← map_mul, ← map_add]
  have h_anti : D1_8_Z * D2_8_Z + D2_8_Z * D1_8_Z = 0 := by decide
  rw [h_anti, map_zero, zero_kronecker]

/-- Commutator `[G_U1, D₁] = (2 : ℝ) • D₂` unlocking the continuous `U(1)` rotation in `Mat16Prod`. -/
theorem comm_G_U1_D1 : comm G_U1_16 D1_16 = (2 : ℝ) • D2_16 := by
  dsimp [comm, G_U1_16, D1_16, D2_16]
  have hGD : (toMat8R (sigmaOp P8_Z A8_Z A8_Z) ⊗ₖ J_phase2) * (toMat8R D1_8_Z ⊗ₖ I2_R) =
      (toMat8R (sigmaOp P8_Z A8_Z A8_Z) * toMat8R D1_8_Z) ⊗ₖ (J_phase2 * I2_R) := by
    rw [← Matrix.mul_kronecker_mul]
  have hDG : (toMat8R D1_8_Z ⊗ₖ I2_R) * (toMat8R (sigmaOp P8_Z A8_Z A8_Z) ⊗ₖ J_phase2) =
      (toMat8R D1_8_Z * toMat8R (sigmaOp P8_Z A8_Z A8_Z)) ⊗ₖ (I2_R * J_phase2) := by
    rw [← Matrix.mul_kronecker_mul]
  rw [hGD, hDG, mul_I2_R, I2_R_mul]
  rw [← sub_kronecker, ← map_mul, ← map_mul, ← map_sub]
  have hcomm_Z : sigmaOp P8_Z A8_Z A8_Z * D1_8_Z - D1_8_Z * sigmaOp P8_Z A8_Z A8_Z = 2 * D2_8_Z := by decide
  rw [hcomm_Z, toMat8R_two_mul, kronecker_smul_left]

/-- Exact BdG dispersion gap: `Delta_U1(θ)² = V16` for all angles `θ : ℝ`. -/
theorem delta_U1_sq (θ : ℝ) :
    Delta_U1 θ * Delta_U1 θ = V16 := by
  dsimp [Delta_U1]
  calc
    (Real.cos θ • D1_16 + Real.sin θ • D2_16) * (Real.cos θ • D1_16 + Real.sin θ • D2_16)
      = (Real.cos θ ^ 2) • (D1_16 * D1_16) +
        (Real.cos θ * Real.sin θ) • (D1_16 * D2_16 + D2_16 * D1_16) +
        (Real.sin θ ^ 2) • (D2_16 * D2_16) := by
        simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, add_assoc]
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
    _ = (Real.cos θ ^ 2) • V16 + (Real.cos θ * Real.sin θ) • (0 : Mat16Prod) + (Real.sin θ ^ 2) • V16 := by
        rw [d1_16_sq, d2_16_sq, anticomm_d1_d2_16]
    _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) • V16 := by
        simp only [smul_zero, add_zero, add_smul]
    _ = V16 := by
        rw [Real.cos_sq_add_sin_sq, one_smul]

/-! ### Part 3: Custodial Twin Involution & All-Loop Polynomial Vanishing -/

/-- Custodial twin-exchange involution in `Mat₈(ℤ)`: `W_twin = Φ + P₀`. -/
def W_twin_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  phiOp P8_Z A8_Z A8_Z + (1 - casimirV P8_Z A8_Z A8_Z)

/-- Lifted custodial twin involution in `Mat16Prod`: `W_twin16 = W_twin_Z ⊗ I₂`. -/
def W_twin16 : Mat16Prod := toMat8R W_twin_Z ⊗ₖ I2_R

/-- Master algebraic relations of the custodial twin involution `W_twin_Z` in `Mat₈(ℤ)`. -/
theorem custodial_twin_involution_Z :
    W_twin_Z * W_twin_Z = 1 ∧
    W_twin_Z.transpose = W_twin_Z ∧
    W_twin_Z * H_hor_Z = H_hor_Z * W_twin_Z ∧
    W_twin_Z * (1 - casimirV P8_Z A8_Z A8_Z) = 1 - casimirV P8_Z A8_Z A8_Z ∧
    (1 - casimirV P8_Z A8_Z A8_Z) * W_twin_Z = 1 - casimirV P8_Z A8_Z A8_Z ∧
    W_twin_Z * D1_8_Z * W_twin_Z = -D1_8_Z := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- All-loop polynomial odd-power vanishing:
    for all polynomials `F, G ∈ ℝ[X]` and all `m : ℕ`, the sandwich
    `P₀ F(H_hor) D₁^(2m+1) G(H_hor) P₀ = 0` identically vanishes. -/
theorem custodial_all_loop_odd_power_vanishing
    (F G : Polynomial ℝ) (m : ℕ) :
    let P0_8_R := toMat8R (1 - casimirV P8_Z A8_Z A8_Z)
    P0_8_R * Polynomial.aeval (toMat8R H_hor_Z) F *
      (toMat8R D1_8_Z) ^ (2 * m + 1) *
      Polynomial.aeval (toMat8R H_hor_Z) G * P0_8_R = 0 := by
  intro P0_8_R
  let W := toMat8R W_twin_Z
  let H := toMat8R H_hor_Z
  let D1 := toMat8R D1_8_Z
  let A := Polynomial.aeval H F
  let C := Polynomial.aeval H G
  have hW : W * W = 1 := by
    rw [← map_mul, show W_twin_Z * W_twin_Z = 1 by decide, map_one]
  have hWP : W * P0_8_R = P0_8_R := by
    rw [← map_mul, show W_twin_Z * (1 - casimirV P8_Z A8_Z A8_Z) =
      1 - casimirV P8_Z A8_Z A8_Z by decide]
  have hPW : P0_8_R * W = P0_8_R := by
    rw [← map_mul, show (1 - casimirV P8_Z A8_Z A8_Z) * W_twin_Z =
      1 - casimirV P8_Z A8_Z A8_Z by decide]
  have hWH : W * H = H * W := by
    rw [← map_mul, ← map_mul, show W_twin_Z * H_hor_Z = H_hor_Z * W_twin_Z by decide]
  have hAW : W * A = A * W := aeval_commutes_of_comm hWH F
  have hCW : W * C = C * W := aeval_commutes_of_comm hWH G
  have hWD1 : W * D1 = -D1 * W := by
    have h_anti : W_twin_Z * D1_8_Z = -(D1_8_Z * W_twin_Z) := by decide
    calc W * D1 = toMat8R (W_twin_Z * D1_8_Z) := by rw [map_mul]
      _ = toMat8R (-(D1_8_Z * W_twin_Z)) := by rw [h_anti]
      _ = -toMat8R (D1_8_Z * W_twin_Z) := map_neg toMat8R _
      _ = -(toMat8R D1_8_Z * toMat8R W_twin_Z) := by rw [map_mul]
      _ = -(D1 * W) := by rfl
      _ = -D1 * W := (neg_mul D1 W).symm
  have h2 : ∀ z : Matrix (Fin 8) (Fin 8) ℝ, z + z = 0 → z = 0 := by
    intro z hz
    ext i j
    have hij := congr_fun (congr_fun hz i) j
    have hij_add : (z + z) i j = z i j + z i j := rfl
    have hij_zero : (0 : Matrix (Fin 8) (Fin 8) ℝ) i j = 0 := rfl
    rw [hij_add, hij_zero] at hij
    linarith
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.custodial_corner_odd_power_sandwich_eq_zero
    W P0_8_R A D1 C m hW hWP hPW hAW hCW hWD1 h2

/-- Lorentz boost invariance of even powers in `Mat16Prod`:
    `K8_16` anticommutes with `D1_16`, hence commutes with all even powers `D1_16 ^ (2 * m)`. -/
theorem custodial_boost_comm_even_powers (m : ℕ) :
    W_twin16 * W_twin16 = 1 ∧
    K8_16 * (D1_16 ^ (2 * m)) - (D1_16 ^ (2 * m)) * K8_16 = 0 := by
  have hW16 : W_twin16 * W_twin16 = 1 := by
    dsimp [W_twin16]
    rw [← Matrix.mul_kronecker_mul, ← map_mul,
        show W_twin_Z * W_twin_Z = 1 by decide,
        map_one, I2_R_mul_I2_R, one_kronecker_I2_R]
  refine ⟨hW16, ?_⟩
  have hKD : K8_16 * D1_16 = -D1_16 * K8_16 := by
    dsimp [K8_16, D1_16]
    rw [neg_mul]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, I2_R_mul_I2_R]
    rw [← map_mul, ← map_mul]
    have hKD_Z : K8_Z * D1_8_Z = -(D1_8_Z * K8_Z) := by decide
    rw [hKD_Z, map_neg, neg_kronecker]
  have heven := InfoGeometry.OperatorAlgebra.PeirceSpine.exchange_commutes_even_power
    K8_16 D1_16 hKD m
  rw [heven, sub_self]

/-! ### Part 4: 1-Loop Parity-Odd Cosmic Birefringence -/

/-- Parity-odd birefringence matrix generator in `Mat₈(ℤ)`: `M_biref = (P₀ + G₈) J_spin`. -/
def M_biref_Z : Matrix (Fin 8) (Fin 8) ℤ :=
  (1 - casimirV P8_Z A8_Z A8_Z + G8_Z) * J8_spin_Z

/-- Explicit 1-loop birefringence matrix in `Mat16Prod`: `M_biref = M_biref_Z ⊗ J_phase2`. -/
def M_biref : Mat16Prod :=
  toMat8R M_biref_Z ⊗ₖ J_phase2

/-- 1-loop parity-odd cosmic birefringence theorem:
    in `Mat16Prod`, the horizon sandwich of `Delta_U1(θ)` vanishes identically at `θ = 0`,
    while inducing an exact parity-odd polarization rotation `(2 * sin(θ)) • M_biref` at `θ ≠ 0`. -/
theorem one_loop_parity_odd_birefringence (θ : ℝ) :
    let H16 : Mat16Prod := toMat8R H_hor_Z ⊗ₖ I2_R
    P0_16 * H16 * Delta_U1 θ * H16 * P0_16 = (2 * Real.sin θ) • M_biref := by
  intro H16
  dsimp [Delta_U1]
  let P0_Z := 1 - casimirV P8_Z A8_Z A8_Z
  have hP0_H_D1 : P0_16 * H16 * D1_16 * H16 * P0_16 = 0 := by
    dsimp [P0_16, H16, D1_16]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [I2_R_mul_I2_R]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    have hZ : P0_Z * H_hor_Z * D1_8_Z * H_hor_Z * P0_Z = 0 := by decide
    rw [hZ, map_zero, zero_kronecker]
  have hP0_H_D2 : P0_16 * H16 * D2_16 * H16 * P0_16 = (2 : ℝ) • M_biref := by
    dsimp [P0_16, H16, D2_16, M_biref]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [I2_R_mul, mul_I2_R]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    have hZ : P0_Z * H_hor_Z * D2_8_Z * H_hor_Z * P0_Z = 2 * M_biref_Z := by decide
    rw [hZ, toMat8R_two_mul, kronecker_smul_left]
  calc
    P0_16 * H16 * (Real.cos θ • D1_16 + Real.sin θ • D2_16) * H16 * P0_16
      = Real.cos θ • (P0_16 * H16 * D1_16 * H16 * P0_16) +
        Real.sin θ • (P0_16 * H16 * D2_16 * H16 * P0_16) := by
        simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    _ = Real.cos θ • (0 : Mat16Prod) + Real.sin θ • ((2 : ℝ) • M_biref) := by
        rw [hP0_H_D1, hP0_H_D2]
    _ = (2 * Real.sin θ) • M_biref := by
        simp only [smul_zero, zero_add, smul_smul]
        ring_nf

/-! ### Part 5: Josephson Cosine Coupling & Sub-Isometric Off-Shell Defect -/

/-- Trace of `casimirV` in `M₈(ℝ)` is exactly 4. -/
lemma toMat8R_casimirV_trace :
    (toMat8R (casimirV P8_Z A8_Z A8_Z)).trace = 4 := by
  have hV_Z : casimirV P8_Z A8_Z A8_Z = Matrix.diagonal ![1, 1, 0, 0, 0, 0, 1, 1] := by decide
  rw [hV_Z]
  simp only [toMat8R, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.trace, Matrix.diag,
             Fin.sum_univ_eight, Int.coe_castRingHom]
  norm_num

lemma v16_trace : V16.trace = 8 := by
  dsimp [V16]
  rw [Matrix.trace_kronecker, toMat8R_casimirV_trace, I2_R_trace]
  norm_num

lemma d1_d2_16_trace : (D1_16 * D2_16).trace = 0 := by
  dsimp [D1_16, D2_16]
  rw [← Matrix.mul_kronecker_mul, I2_R_mul]
  rw [Matrix.trace_kronecker, J_phase2_trace, mul_zero]

lemma d2_d1_16_trace : (D2_16 * D1_16).trace = 0 := by
  dsimp [D1_16, D2_16]
  rw [← Matrix.mul_kronecker_mul, mul_I2_R]
  rw [Matrix.trace_kronecker, J_phase2_trace, mul_zero]

/-- Josephson cosine hopping coupling:
    the trace of the product of two condensates at phase angles `θx, θy`
    equals `8 * cos(θx - θy)`. -/
theorem josephson_cosine_coupling (θx θy : ℝ) :
    (Delta_U1 θx * Delta_U1 θy).trace = 8 * Real.cos (θx - θy) := by
  dsimp [Delta_U1]
  simp only [add_mul, mul_add, Matrix.trace_add, smul_mul_assoc, mul_smul_comm,
             Matrix.trace_smul, d1_16_sq, d2_16_sq, v16_trace,
             d1_d2_16_trace, d2_d1_16_trace]
  rw [Real.cos_sub θx θy]
  ring

/-- Quadratic Casimir defect operator `casimirDefect(X) = X² - X`. -/
def casimirDefect (X : Mat16Prod) : Mat16Prod := X * X - X

/-- Continuous sub-isometric infrared horizon defect `V16_eps(ε) = (1 - ε) • V16`. -/
def V16_eps (ε : ℝ) : Mat16Prod := (1 - ε) • V16

/-- Sub-isometric off-shell defect theorem:
    under the continuous deformation `V16_eps(ε)`, the quadratic defect
    evaluates to `(-ε * (1 - ε)) • V16`, vanishing continuously as `ε → 0`. -/
theorem casimirDefect_V16_eps (ε : ℝ) :
    casimirDefect (V16_eps ε) = (-ε * (1 - ε)) • V16 := by
  dsimp [casimirDefect, V16_eps]
  have hV_sq : V16 * V16 = V16 := by
    dsimp [V16]
    rw [← Matrix.mul_kronecker_mul, ← map_mul,
        show casimirV P8_Z A8_Z A8_Z * casimirV P8_Z A8_Z A8_Z = casimirV P8_Z A8_Z A8_Z by decide,
        I2_R_mul_I2_R]
  calc
    ((1 - ε) • V16) * ((1 - ε) • V16) - (1 - ε) • V16
      = ((1 - ε) * (1 - ε)) • (V16 * V16) - (1 - ε) • V16 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = ((1 - ε) * (1 - ε) - (1 - ε)) • V16 := by
        rw [hV_sq, ← sub_smul]
    _ = (-ε * (1 - ε)) • V16 := by
        have hring : (1 - ε) * (1 - ε) - (1 - ε) = -ε * (1 - ε) := by ring
        rw [hring]

/-! ### Part 6: OpenGauss T16 Non-Commutativity Witness -/

/-- OpenGauss T16 non-commutativity witness on `Mat16Prod`:
    the phase generator `G_U1_16` and discrete BdG operator `D1_16` do not commute. -/
lemma custodial_mat16_noncomm : ∃ A B : Mat16Prod, A * B ≠ B * A := by
  refine ⟨G_U1_16, D1_16, ?_⟩
  intro hcomm
  have hcomm_zero : comm G_U1_16 D1_16 = 0 := by
    dsimp [comm]; rw [hcomm, sub_self]
  have h2D2 : (2 : ℝ) • D2_16 = 0 := by
    rw [← comm_G_U1_D1, hcomm_zero]
  have h_entry := congr_fun (congr_fun h2D2 (0, 1)) (7, 0)
  simp only [D2_16, Matrix.smul_apply, Matrix.zero_apply,
             Matrix.kroneckerMap_apply, toMat8R, RingHom.mapMatrix_apply,
             Matrix.map_apply, Int.coe_castRingHom] at h_entry
  have hD2_07 : D2_8_Z 0 7 = 1 := by decide
  have hJ_10 : J_phase2 1 0 = 1 := by
    simp [J_phase2]
  rw [hD2_07, hJ_10] at h_entry
  norm_num at h_entry

/-- OpenGauss T16 non-commutativity witness on `Matrix (Fin 8) (Fin 8) ℝ`. -/
lemma custodial_matrix8_R_noncomm : ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A :=
  clifford8_matrix_R_noncomm

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich

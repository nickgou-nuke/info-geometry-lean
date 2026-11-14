/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Noncommutative Future Horizons Tower (`N₁`–`N₅`)

Formalizes over arbitrary noncommutative rings `[Ring B]` and `[Ring A] [StarRing A]`
the five higher-order horizons (`N₁`–`N₅`):
1. `N₁`: Arbitrary-`n` inductive Clifford–Tetraktys tower `ClTower n A ≅ M_{2^n}(A)`,
   recursive Cantor corner projection `cantorTowerProj`, recursive Clifford–Cayley–Walsh
   transform `cayleyTowerOp`, and all-scales `2⁻ⁿ` Cantor localization contraction.
2. `N₂`: Connes' spectral triple calculus on `M₂(A)`, quantized differential `connesDiff D E = ⁅D, E⁆`,
   anticommutator on odd 1-forms, and graded cochain curvature `connesDiff D (connesDiff D X) = ⁅D * D, X⁆`.
3. `N₃`: Noncommutative geodesic duality `D (rightWindingForm D X) = X * D (windingForm D X) * X⁻¹`
   and Levi-Civita parallel transport `burgSteinHessian X (X * V₀ * X) = V₀`.
4. `N₄`: Multi-strand Artin braid group `B₄` relations (adjacent Yang–Baxter and far-commutativity)
   for skew-involutive bivectors `E₁₂, E₂₃, E₃₄`.
5. `N₅`: Multiresolution `n`-scale RG block decimation `rgTowerDecimate` and partition trace
   conservation `towerTrace (n + 1) M = towerTrace n (rgTowerDecimate n M)`.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

/-- Explicit `2 × 2` matrix constructor avoiding `vecCons`/`vecMul` simp expansion. -/
def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  fun i j => match i, j with
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

omit [Ring A] in @[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
omit [Ring A] in @[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
omit [Ring A] in @[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
omit [Ring A] in @[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

omit [Ring A] in @[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 0 0 = star (M 0 0) := rfl
omit [Ring A] in @[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 0 1 = star (M 1 0) := rfl
omit [Ring A] in @[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 1 0 = star (M 0 1) := rfl
omit [Ring A] in @[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 1 1 = star (M 1 1) := rfl

def gamma1Op : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)

end Matrix2Simp

/-!
## Horizon N₁ & N₅: The Arbitrary-n Inductive Clifford–Tetraktys Tower Cl_n(A), All-Scales 2⁻ⁿ Cantor FUP & RG Trace Conservation
-/

section HorizonN1_N5_InductiveCliffordTower

universe u

/-- The `n`-scale inductive dyadic operator tower `ClTower n A ≅ M_{2^n}(A) ≅ Cl(n,n) ⊗ A`. -/
@[reducible] def ClTower : ℕ → Type u → Type u
  | 0, A     => A
  | n + 1, A => Matrix (Fin 2) (Fin 2) (ClTower n A)

@[reducible] instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower n A)
  | 0     => inferInstance
  | n + 1 =>
      let _ : Ring (ClTower n A) := instRingClTower n
      inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower n A)))

@[reducible] instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower n A)
  | 0     => inferInstance
  | n + 1 =>
      let _ : Ring (ClTower n A) := instRingClTower n
      let _ : StarRing (ClTower n A) := instStarRingClTower n
      inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower n A)))

variable {A : Type u} [Ring A]

/-- The `n`-scale Cantor corner projection `Π_{C_n} ∈ ClTower n A`. -/
def cantorTowerProj : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorTowerProj n) 0 0 0

/-- The `n`-scale recursive Clifford–Cayley–Walsh transform `U_n ∈ ClTower n A`. -/
def cayleyTowerOp : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (cayleyTowerOp n) (-cayleyTowerOp n) (cayleyTowerOp n) (cayleyTowerOp n)

/-- Single-step RG block decimation `R_RG : ClTower (n + 1) A → ClTower n A`. -/
def rgTowerDecimate (n : ℕ) (M : ClTower (n + 1) A) : ClTower n A :=
  M 0 0 + M 1 1

/-- Iterated `n`-scale partition trace `Tr_{2^n} : ClTower n A → A`. -/
def towerTrace : ∀ n : ℕ, ClTower n A → A
  | 0, a     => a
  | n + 1, M => towerTrace n (rgTowerDecimate n M)

theorem towerTrace_add : ∀ (n : ℕ) (X Y : ClTower n A),
    towerTrace n (X + Y) = towerTrace n X + towerTrace n Y
  | 0, X, Y     => rfl
  | n + 1, X, Y => by
      change towerTrace n (((X + Y) 0 0) + ((X + Y) 1 1)) =
        towerTrace n (X 0 0 + X 1 1) + towerTrace n (Y 0 0 + Y 1 1)
      have h_rearrange : (X + Y) 0 0 + (X + Y) 1 1 =
          (X 0 0 + X 1 1) + (Y 0 0 + Y 1 1) := by
        simp only [Matrix.add_apply]
        abel
      rw [h_rearrange]
      rw [towerTrace_add n]

theorem towerTrace_zero : ∀ (n : ℕ), towerTrace n (0 : ClTower n A) = 0
  | 0 => rfl
  | n + 1 => by
      simp [towerTrace, rgTowerDecimate, towerTrace_zero n]

theorem towerTrace_neg : ∀ (n : ℕ) (X : ClTower n A),
    towerTrace n (-X) = -towerTrace n X
  | 0, X => rfl
  | n + 1, X => by
      change towerTrace n ((-X) 0 0 + (-X) 1 1) =
        -towerTrace n (X 0 0 + X 1 1)
      calc towerTrace n ((-X) 0 0 + (-X) 1 1)
          = towerTrace n (-(X 0 0 + X 1 1)) := by
              congr 1
              simp only [Matrix.neg_apply]
              abel
        _ = -towerTrace n (X 0 0 + X 1 1) := towerTrace_neg n _

theorem cantorTowerProj_idem : ∀ n : ℕ,
    (cantorTowerProj n : ClTower n A) * cantorTowerProj n = cantorTowerProj n
  | 0 => mul_one 1
  | n + 1 => by
      apply ext_fin2 <;> simp [cantorTowerProj, cantorTowerProj_idem n]

theorem towerTrace_cantor_normalization (n : ℕ) :
    towerTrace n (cantorTowerProj n : ClTower n A) = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change towerTrace k (cantorTowerProj k + 0) = 1
      simpa using ih

theorem towerTrace_identity_normalization (n : ℕ) :
    towerTrace n (1 : ClTower n A) = (2 ^ n) • (1 : A) := by
  induction n with
  | zero => simp [towerTrace]
  | succ k ih =>
      change towerTrace k ((1 : ClTower k A) + (1 : ClTower k A)) = _
      rw [towerTrace_add, ih, pow_succ']
      simp only [two_mul, add_nsmul]

/-- **All-Scales Inductive RG Trace Conservation & Cantor Ground-State Normalization (`N₅`)**:
For every scale `n ∈ ℕ`:
1. `towerTrace (n + 1) M = towerTrace n (rgTowerDecimate n M)`.
2. `towerTrace n (cantorTowerProj n) = 1`.
3. `towerTrace n (1 : ClTower n A) = (2 ^ n) • (1 : A)`. -/
theorem all_scales_rg_trace_and_cantor_normalization (n : ℕ) (M : ClTower (n + 1) A) :
    towerTrace (n + 1) M = towerTrace n (rgTowerDecimate n M) ∧
    towerTrace n (cantorTowerProj n : ClTower n A) = 1 ∧
    towerTrace n (1 : ClTower n A) = (2 ^ n) • (1 : A) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact towerTrace_cantor_normalization n
  · exact towerTrace_identity_normalization n

variable [StarRing A]

/-- **All-Scales Inductive Clifford–Cayley Unitarity & `2⁻ⁿ` Cantor FUP Contraction (`N₁`)**:
For every scale `n ∈ ℕ` in the inductive tower `ClTower n A`:
1. `cantorTowerProj n` is a self-adjoint idempotent.
2. `star (cayleyTowerOp n) * cayleyTowerOp n = (2 ^ n) • 1`.
3. `cantorTowerProj n * cayleyTowerOp n * cantorTowerProj n = cantorTowerProj n`.
4. `star (cayleyTowerOp n * cantorTowerProj n) * (cayleyTowerOp n * cantorTowerProj n) = (2 ^ n) • cantorTowerProj n`
   whereas `star (cantorTowerProj n * cayleyTowerOp n * cantorTowerProj n) * (...) = cantorTowerProj n`. -/
theorem all_scales_inductive_clifford_cantor_fup (n : ℕ) :
    (cantorTowerProj n : ClTower n A) * cantorTowerProj n = cantorTowerProj n ∧
    star (cantorTowerProj n : ClTower n A) = cantorTowerProj n ∧
    star (cayleyTowerOp n : ClTower n A) * cayleyTowerOp n = (2 ^ n) • (1 : ClTower n A) ∧
    (cantorTowerProj n : ClTower n A) * cayleyTowerOp n * cantorTowerProj n = cantorTowerProj n ∧
    star ((cayleyTowerOp n : ClTower n A) * cantorTowerProj n) *
      (cayleyTowerOp n * cantorTowerProj n) = (2 ^ n) • (cantorTowerProj n : ClTower n A) ∧
    star ((cantorTowerProj n : ClTower n A) * cayleyTowerOp n * cantorTowerProj n) *
      (cantorTowerProj n * cayleyTowerOp n * cantorTowerProj n) = cantorTowerProj n := by
  have h_core :
      (cantorTowerProj n : ClTower n A) * cantorTowerProj n = cantorTowerProj n ∧
      star (cantorTowerProj n : ClTower n A) = cantorTowerProj n ∧
      star (cayleyTowerOp n : ClTower n A) * cayleyTowerOp n = (2 ^ n) • (1 : ClTower n A) ∧
      (cantorTowerProj n : ClTower n A) * cayleyTowerOp n * cantorTowerProj n = cantorTowerProj n := by
    induction' n with k ih
    · simp [cantorTowerProj, cayleyTowerOp]
    · rcases ih with ⟨ih_idem, ih_sa, ih_unit, ih_comp⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply ext_fin2 <;> simp [cantorTowerProj, mat2, Matrix.mul_apply, Fin.sum_univ_two, ih_idem]
      · apply ext_fin2 <;> simp [cantorTowerProj, mat2, ih_sa]
      · apply ext_fin2
        · simp [cayleyTowerOp, mat2, Matrix.mul_apply, Fin.sum_univ_two, ih_unit, pow_succ', two_mul]
        · simp [cayleyTowerOp, mat2, Matrix.mul_apply, Fin.sum_univ_two]
        · simp [cayleyTowerOp, mat2, Matrix.mul_apply, Fin.sum_univ_two]
        · simp [cayleyTowerOp, mat2, Matrix.mul_apply, Fin.sum_univ_two, ih_unit, pow_succ', two_mul]
      · apply ext_fin2 <;>
          simp [cantorTowerProj, cayleyTowerOp, mat2, Matrix.mul_apply, Fin.sum_univ_two, ih_comp]
  rcases h_core with ⟨h_idem, h_sa, h_unit, h_comp⟩
  refine ⟨h_idem, h_sa, h_unit, h_comp, ?_, ?_⟩
  · calc star ((cayleyTowerOp n : ClTower n A) * cantorTowerProj n) *
          (cayleyTowerOp n * cantorTowerProj n)
      _ = cantorTowerProj n * (star (cayleyTowerOp n) * cayleyTowerOp n) * cantorTowerProj n := by
          simp only [star_mul, h_sa]; noncomm_ring
      _ = cantorTowerProj n * ((2 ^ n) • (1 : ClTower n A)) * cantorTowerProj n := by rw [h_unit]
      _ = (2 ^ n) • ((cantorTowerProj n : ClTower n A) * cantorTowerProj n) := by
          rw [mul_smul_comm, mul_one, smul_mul_assoc]
      _ = (2 ^ n) • cantorTowerProj n := by rw [h_idem]
  · rw [h_comp, h_sa, h_idem]

end HorizonN1_N5_InductiveCliffordTower

/-!
## Horizon N₂: Connes' Spectral Triple Quantized Differential đf = ⁅D, f⁆ & Graded Cochain Curvature
-/

section HorizonN2_ConnesSpectralTripleCalculus

variable {A : Type*} [Ring A]

/-- Grading involution `γ(X) = Γ₁ X Γ₁` on `M₂(A)`. -/
def gradeInv (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  gamma1Op * X * gamma1Op

/-- Connes' graded Dirac differential `d_D(X) = D X - γ(X) D` on `M₂(A)`. -/
def connesDiff (D X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  D * X - gradeInv X * D

/-- **Connes' Quantized Differential & Graded Curvature Cochain Theorem (`N₂`)**:
For any odd Dirac operator `D = [[0, L₋], [L₊, 0]] ∈ M₂(A)`:
1. On any even operator `E = diag(e₊, e₋)`, `connesDiff D E = ⁅D, E⁆`.
2. On any odd 1-form `Ω₁ = [[0, w₋], [w₊, 0]]`, `connesDiff D Ω₁ = anticomm D Ω₁`.
3. On any operator `X ∈ M₂(A)`, `connesDiff D (connesDiff D X) = ⁅D * D, X⁆`. -/
theorem connes_quantized_differential_and_curvature_cochain
    (L_plus L_minus e_plus e_minus w_plus w_minus : A)
    (X : Matrix (Fin 2) (Fin 2) A) :
    let D   : Matrix (Fin 2) (Fin 2) A := mat2 0 L_minus L_plus 0
    let E   : Matrix (Fin 2) (Fin 2) A := mat2 e_plus 0 0 e_minus
    let Ω_1 : Matrix (Fin 2) (Fin 2) A := mat2 0 w_minus w_plus 0
    connesDiff D E = ⁅D, E⁆ ∧
    connesDiff D Ω_1 = anticomm D Ω_1 ∧
    connesDiff D (connesDiff D X) = ⁅D * D, X⁆ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [connesDiff, gradeInv, gamma1Op]
  · apply ext_fin2 <;> simp [connesDiff, anticomm, gradeInv, gamma1Op]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [connesDiff, gradeInv, gamma1Op] <;> noncomm_ring

end HorizonN2_ConnesSpectralTripleCalculus

/-!
## Horizon N₃: Noncommutative Geodesic Equation & Levi-Civita Parallel Transport of the Burg–Stein Metric
-/

section HorizonN3_NoncommutativeGeodesicsAndParallelTransport

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

theorem IsRingDeriv.map_one {D : B →+ B} (hD : IsRingDeriv D) : D 1 = 0 := by
  have h : D (1 * 1) = D 1 * 1 + 1 * D 1 := hD 1 1
  simp only [mul_one, one_mul] at h
  calc D 1 = D 1 + D 1 - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self (D 1)

theorem IsRingDeriv.map_units_inv {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) :
    D (↑X⁻¹ : B) = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by
  have h1 : D ((X : B) * (↑X⁻¹ : B)) = D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B) :=
    hD (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hD.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) = D (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc D (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by noncomm_ring

def windingForm (D : B →+ B) (X : Bˣ) : B := (↑X⁻¹ : B) * D (X : B)
def rightWindingForm (D : B →+ B) (X : Bˣ) : B := D (X : B) * (↑X⁻¹ : B)
def burgSteinHessian (X : Bˣ) (V : B) : B := (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Noncommutative Geodesic Duality & Levi-Civita Parallel Transport Theorem (`N₃`)**:
1. `D (rightWindingForm D X) = X * D (windingForm D X) * X⁻¹`, so `D (windingForm D X) = 0 ↔ D (rightWindingForm D X) = 0`.
2. Two-sided congruence `V_X = X * V₀ * X` (`D V₀ = 0`) is Levi-Civita parallel transport for
   the Burg–Stein Hessian: `burgSteinHessian X (X * V₀ * X) = V₀` and `D (burgSteinHessian X (X * V₀ * X)) = 0`. -/
theorem noncommutative_geodesic_duality_and_parallel_transport
    {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) {V₀ : B} (hV₀ : D V₀ = 0) :
    D (rightWindingForm D X) = (X : B) * D (windingForm D X) * (↑X⁻¹ : B) ∧
    (D (windingForm D X) = 0 ↔ D (rightWindingForm D X) = 0) ∧
    burgSteinHessian X ((X : B) * V₀ * (X : B)) = V₀ ∧
    D (burgSteinHessian X ((X : B) * V₀ * (X : B))) = 0 := by
  have hX1 : (X : B) * (↑X⁻¹ : B) = 1 := Units.mul_inv X
  have hX2 : (↑X⁻¹ : B) * (X : B) = 1 := Units.inv_mul X
  have h_conj : D (rightWindingForm D X) = (X : B) * D (windingForm D X) * (↑X⁻¹ : B) := by
    have h_eq : rightWindingForm D X = (X : B) * windingForm D X * (↑X⁻¹ : B) := by
      dsimp [rightWindingForm, windingForm]
      calc D (X : B) * (↑X⁻¹ : B)
        _ = ((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) := by rw [hX1, one_mul]
        _ = (X : B) * ((↑X⁻¹ : B) * D (X : B)) * (↑X⁻¹ : B) := by noncomm_ring
    rw [h_eq, hD ((X : B) * windingForm D X) (↑X⁻¹ : B),
        hD (X : B) (windingForm D X), hD.map_units_inv X]
    dsimp [windingForm]
    calc (D (X : B) * ((↑X⁻¹ : B) * D (X : B)) + (X : B) * D ((↑X⁻¹ : B) * D (X : B))) * (↑X⁻¹ : B) +
          (X : B) * ((↑X⁻¹ : B) * D (X : B)) * (-(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B))
      _ = D (X : B) * (↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) -
          ((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) +
          (X : B) * D ((↑X⁻¹ : B) * D (X : B)) * (↑X⁻¹ : B) := by noncomm_ring
      _ = (X : B) * D ((↑X⁻¹ : B) * D (X : B)) * (↑X⁻¹ : B) := by rw [hX1]; noncomm_ring
  have h_hess : burgSteinHessian X ((X : B) * V₀ * (X : B)) = V₀ := by
    dsimp [burgSteinHessian]
    calc (↑X⁻¹ : B) * ((X : B) * V₀ * (X : B)) * (↑X⁻¹ : B)
      _ = ((↑X⁻¹ : B) * (X : B)) * V₀ * ((X : B) * (↑X⁻¹ : B)) := by noncomm_ring
      _ = V₀ := by rw [hX2, hX1]; noncomm_ring
  refine ⟨h_conj, ?_, h_hess, by rw [h_hess, hV₀]⟩
  constructor
  · intro h0; rw [h_conj, h0]; noncomm_ring
  · intro h0
    calc D (windingForm D X)
      _ = ((↑X⁻¹ : B) * (X : B)) * D (windingForm D X) * ((↑X⁻¹ : B) * (X : B)) := by
          rw [hX2]; noncomm_ring
      _ = (↑X⁻¹ : B) * ((X : B) * D (windingForm D X) * (↑X⁻¹ : B)) * (X : B) := by noncomm_ring
      _ = (↑X⁻¹ : B) * D (rightWindingForm D X) * (X : B) := by rw [← h_conj]
      _ = 0 := by rw [h0]; noncomm_ring

end HorizonN3_NoncommutativeGeodesicsAndParallelTransport

/-!
## Horizon N₄: Multi-Strand Artin Braid Group B_N (Adjacent Yang–Baxter + Far-Commutativity)
-/

section HorizonN4_MultiStrandArtinBraidGroup

variable {B : Type*} [Ring B]

theorem clifford_bivector_triple_product {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := by
  have h12' : E₁₂ * E₁₂ + 1 = 0 := by rw [h12]; abel
  calc (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
    _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
        (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by noncomm_ring
    _ = 2 * (E₁₂ + E₂₃) + 0 * (1 - E₂₃) + (1 + E₁₂) * 0 := by rw [h12', h_anti]
    _ = 2 * (E₁₂ + E₂₃) := by noncomm_ring

/-- **Multi-Strand Clifford–Majorana Artin Braid Group Theorem (`N₄`)**:
For any chain of skew-involutive bivectors `E₁₂, E₂₃, E₃₄ ∈ B` (`E² = -1`) where adjacent
bivectors anticommute and disjoint bivectors commute (`⁅E₁₂, E₃₄⁆ = 0`), the braid operators
`R₁ = 1 + E₁₂`, `R₂ = 1 + E₂₃`, `R₃ = 1 + E₃₄` satisfy all defining relations of the
4-strand Artin braid group `B₄`. -/
theorem multi_strand_artin_braid_group_relations
    {E₁₂ E₂₃ E₃₄ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h23 : E₂₃ * E₂₃ = -1) (h34 : E₃₄ * E₃₄ = -1)
    (h_anti12 : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0)
    (h_anti23 : E₂₃ * E₃₄ + E₃₄ * E₂₃ = 0)
    (h_far13  : ⁅E₁₂, E₃₄⁆ = 0) :
    let R₁ := 1 + E₁₂
    let R₂ := 1 + E₂₃
    let R₃ := 1 + E₃₄
    R₁ * R₂ * R₁ = R₂ * R₁ * R₂ ∧
    R₂ * R₃ * R₂ = R₃ * R₂ * R₃ ∧
    R₁ * R₃ = R₃ * R₁ := by
  have h_anti21 : E₂₃ * E₁₂ + E₁₂ * E₂₃ = 0 := by rw [add_comm, h_anti12]
  have h_anti32 : E₃₄ * E₂₃ + E₂₃ * E₃₄ = 0 := by rw [add_comm, h_anti23]
  refine ⟨?_, ?_, ?_⟩
  · rw [clifford_bivector_triple_product h12 h_anti12,
        clifford_bivector_triple_product h23 h_anti21]
    noncomm_ring
  · rw [clifford_bivector_triple_product h23 h_anti23,
        clifford_bivector_triple_product h34 h_anti32]
    noncomm_ring
  · rw [Ring.lie_def] at h_far13
    have h_comm : E₁₂ * E₃₄ = E₃₄ * E₁₂ := sub_eq_zero.mp h_far13
    calc (1 + E₁₂) * (1 + E₃₄) = 1 + E₁₂ + E₃₄ + E₁₂ * E₃₄ := by noncomm_ring
      _ = 1 + E₁₂ + E₃₄ + E₃₄ * E₁₂ := by rw [h_comm]
      _ = (1 + E₃₄) * (1 + E₁₂) := by noncomm_ring

end HorizonN4_MultiStrandArtinBraidGroup


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower

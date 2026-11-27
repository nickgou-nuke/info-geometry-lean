/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.GroupTheory.Perm.Basic
import proofs.BraidProject.BraidGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ConnesLottYangBaxterPoset
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Canonical.HeckeBraidTopologicalBridge
import InfoGeometry.Categorical.UniversalArtinBraidRepresentation
import InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
import InfoGeometry.Categorical.HadjiivanovBraidGroupColimit
import InfoGeometry.OperatorAlgebra.QCCRResidual
import InfoGeometry.Canonical.CreationAnnihilationTomitaBridge

/-!
# q-Deformed Braid Interpolation, Non-Scalar Spectral Yang–Baxter & CAR/CCR Collapse

Formalizes:
1. Genuine non-scalar `8 × 8` complex Yang rational spectral Yang–Baxter equation
   `yangR12 (u - v) η * yangR13 u η * yangR23 v η = yangR23 v η * yangR13 u η * yangR12 (u - v) η`
   on `Matrix (Fin 8) (Fin 8) ℂ` (`u • 1 + η • Pᵢⱼ`), with explicit T16 witness;
2. Universal associative-algebra `HeckeGeneratorPair` and Baxterized spectral Yang–Baxter
   equation `baxterized_yang_baxter`, connected to `HeckeBraidTopologicalBridge.leftMulTopCatHom`,
   plus concrete `4 × 4` / `8 × 8` Jimbo `q`-Hecke matrices (`checkR q`, `heckeT1 q`, `heckeT2 q`,
   specializing to Fibonacci `YangBaxterProof.q`, bosonic swap `q = 1`, and fermionic signed swap
   `q = -1`) and the `8 × 8` trigonometric spectral Yang–Baxter equation `hecke_8x8_spectral_yang_baxter`;
3. Genuine axiom-free `q`-parameterized representations of `Braid.braid_group (m + 1)` and
   `Braid.braid_group_inf` (`B_∞`) on `FockConfigSpace := (ℕ → Bool) → ℂ`, compatible under
   `finiteToInfiniteGroupHom`, collapsing cleanly to the bosonic CCR symmetric swap at `q = 1`
   and the fermionic CAR signed swap at `q = -1`, plus `qBracket` bridging to `QCCRResidual` and
   `SuperchargeCARCCRBridge.CARBracket` / `CCRBracket`.
-/

noncomputable section

namespace InfoGeometry.Quantum.BraidInterpolation

open Matrix
open CategoryTheory
open Braid
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Canonical.HeckeBraidTopologicalBridge
open InfoGeometry.Categorical.UniversalArtinBraidRepresentation
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Categorical.HadjiivanovBraidGroupColimit
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

/-! ## 1. Non-Scalar `8 × 8` Yang Rational Spectral Yang–Baxter Equation -/

/-- Swap bits `2` and `1` in `Fin 8` (acting on tensor factors `1 ↔ 2` of `(ℂ²)⊗³`). -/
def swap12 (i : Fin 8) : Fin 8 :=
  ⟨((i.val / 2) % 2) * 4 + (i.val / 4) * 2 + (i.val % 2), by omega⟩

/-- Swap bits `1` and `0` in `Fin 8` (acting on tensor factors `2 ↔ 3` of `(ℂ²)⊗³`). -/
def swap23 (i : Fin 8) : Fin 8 :=
  ⟨(i.val / 4) * 4 + (i.val % 2) * 2 + ((i.val / 2) % 2), by omega⟩

/-- Swap bits `2` and `0` in `Fin 8` (acting on tensor factors `1 ↔ 3` of `(ℂ²)⊗³`). -/
def swap13 (i : Fin 8) : Fin 8 :=
  ⟨(i.val % 2) * 4 + ((i.val / 2) % 2) * 2 + (i.val / 4), by omega⟩

theorem swap12_comp_swap12 : swap12 ∘ swap12 = id := by
  funext i; fin_cases i <;> decide

theorem swap23_comp_swap23 : swap23 ∘ swap23 = id := by
  funext i; fin_cases i <;> decide

theorem swap13_comp_swap13 : swap13 ∘ swap13 = id := by
  funext i; fin_cases i <;> decide

theorem swap13_comp_swap12 : swap13 ∘ swap12 = swap12 ∘ swap23 := by
  funext i; fin_cases i <;> decide

theorem swap23_comp_swap13 : swap23 ∘ swap13 = swap13 ∘ swap12 := by
  funext i; fin_cases i <;> decide

theorem swap12_comp_swap13 : swap12 ∘ swap13 = swap23 ∘ swap12 := by
  funext i; fin_cases i <;> decide

theorem swap13_comp_swap23 : swap13 ∘ swap23 = swap12 ∘ swap13 := by
  funext i; fin_cases i <;> decide

theorem swap23_comp_swap13_comp_swap12 : swap23 ∘ (swap13 ∘ swap12) = swap13 := by
  funext i; fin_cases i <;> decide

theorem swap12_comp_swap13_comp_swap23 : swap12 ∘ (swap13 ∘ swap23) = swap13 := by
  funext i; fin_cases i <;> decide

/-- Permutation matrix on `Fin 8` associated to a function `f : Fin 8 → Fin 8`. -/
def swapMat (f : Fin 8 → Fin 8) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if f i = j then 1 else 0

theorem swapMat_id : swapMat id = 1 := by
  ext i j
  simp [swapMat, Matrix.one_apply]

theorem swapMat_mul (f g : Fin 8 → Fin 8) :
    swapMat f * swapMat g = swapMat (g ∘ f) := by
  ext i k
  simp only [Matrix.mul_apply, swapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · intro hi
    exact absurd (Finset.mem_univ (f i)) hi

theorem swapMat_mul_left (f : Fin 8 → Fin 8) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    swapMat f * M = Matrix.of fun i j => M (f i) j := by
  ext i j
  simp only [Matrix.mul_apply, swapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro k _ hk
    simp [hk.symm]
  · intro hi
    exact absurd (Finset.mem_univ (f i)) hi

theorem mul_swapMat_right (M : Matrix (Fin 8) (Fin 8) ℂ) (g g_inv : Fin 8 → Fin 8)
    (hinv : ∀ k j : Fin 8, g k = j ↔ k = g_inv j) :
    M * swapMat g = Matrix.of fun i j => M i (g_inv j) := by
  ext i j
  simp only [Matrix.mul_apply, swapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (g_inv j)]
  · simp [(hinv (g_inv j) j).mpr rfl]
  · intro k _ hk
    have hgk : g k ≠ j := fun h => hk ((hinv k j).mp h)
    simp [hgk]
  · intro hi
    exact absurd (Finset.mem_univ (g_inv j)) hi

/-- Swap operator `P₁₂` on `(ℂ²)⊗³`. -/
def P12 : Matrix (Fin 8) (Fin 8) ℂ := swapMat swap12

/-- Swap operator `P₂₃` on `(ℂ²)⊗³`. -/
def P23 : Matrix (Fin 8) (Fin 8) ℂ := swapMat swap23

/-- Swap operator `P₁₃` on `(ℂ²)⊗³`. -/
def P13 : Matrix (Fin 8) (Fin 8) ℂ := swapMat swap13

theorem P12_sq : P12 * P12 = 1 := by
  rw [P12, swapMat_mul, swap12_comp_swap12, swapMat_id]

theorem P23_sq : P23 * P23 = 1 := by
  rw [P23, swapMat_mul, swap23_comp_swap23, swapMat_id]

theorem P13_sq : P13 * P13 = 1 := by
  rw [P13, swapMat_mul, swap13_comp_swap13, swapMat_id]

theorem P12_P13_eq_P23_P12 : P12 * P13 = P23 * P12 := by
  rw [P12, P13, P23, swapMat_mul, swapMat_mul, swap13_comp_swap12]

theorem P13_P23_eq_P12_P13 : P13 * P23 = P12 * P13 := by
  rw [P13, P23, P12, swapMat_mul, swapMat_mul, swap23_comp_swap13, swap13_comp_swap12]

theorem P13_P12_eq_P12_P23 : P13 * P12 = P12 * P23 := by
  rw [P13, P12, P23, swapMat_mul, swapMat_mul, swap12_comp_swap13]

theorem P23_P13_eq_P13_P12 : P23 * P13 = P13 * P12 := by
  rw [P23, P13, P12, swapMat_mul, swapMat_mul, swap13_comp_swap23, swap12_comp_swap13]

theorem P12_P13_P23_eq_P13 : P12 * P13 * P23 = P13 := by
  rw [P12, P13, P23, swapMat_mul, swapMat_mul, swap23_comp_swap13_comp_swap12]

theorem P23_P13_P12_eq_P13 : P23 * P13 * P12 = P13 := by
  rw [P23, P13, P12, swapMat_mul, swapMat_mul, swap12_comp_swap13_comp_swap23]

theorem P13_eq_P12_P23_P12 : P13 = P12 * P23 * P12 := by
  rw [← P13_P12_eq_P12_P23, Matrix.mul_assoc, P12_sq, mul_one]

theorem P13_eq_P23_P12_P23 : P13 = P23 * P12 * P23 := by
  rw [← P23_P13_P12_eq_P13, Matrix.mul_assoc, P13_P12_eq_P12_P23, ← Matrix.mul_assoc]

/-- Yang's rational spectral R-matrix `R₁₂(u, η) = u I + η P₁₂` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def yangR12 (u η : ℂ) : Matrix (Fin 8) (Fin 8) ℂ := u • 1 + η • P12

/-- Yang's rational spectral R-matrix `R₁₃(u, η) = u I + η P₁₃` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def yangR13 (u η : ℂ) : Matrix (Fin 8) (Fin 8) ℂ := u • 1 + η • P13

/-- Yang's rational spectral R-matrix `R₂₃(u, η) = u I + η P₂₃` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def yangR23 (u η : ℂ) : Matrix (Fin 8) (Fin 8) ℂ := u • 1 + η • P23

/-- Genuine non-scalar `8 × 8` Yang rational spectral Yang–Baxter equation. -/
theorem yang_spectral_yang_baxter (u v η : ℂ) :
    yangR12 (u - v) η * yangR13 u η * yangR23 v η =
      yangR23 v η * yangR13 u η * yangR12 (u - v) η := by
  simp only [yangR12, yangR13, yangR23, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  rw [P12_P13_P23_eq_P13, P23_P13_P12_eq_P13, P13_P23_eq_P12_P13, P12_P13_eq_P23_P12,
    P23_P13_eq_P13_P12, P13_P12_eq_P12_P23]
  ext i j
  simp
  ring

/-- Binder-free T16 non-commutativity witness for `Matrix (Fin 8) (Fin 8) ℂ`:
    `P₁₂ * P₂₃ ≠ P₂₃ * P₁₂` (and hence `yangR12 0 1 * yangR23 0 1 ≠ yangR23 0 1 * yangR12 0 1`). -/
theorem P12_P23_noncomm : P12 * P23 ≠ P23 * P12 := by
  intro h
  have h12 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ => M 1 2) h
  simp [P12, P23, swapMat, swap12, swap23, Matrix.mul_apply] at h12

theorem yangR12_yangR23_noncomm :
    yangR12 0 1 * yangR23 0 1 ≠ yangR23 0 1 * yangR12 0 1 := by
  simpa [yangR12, yangR23] using P12_P23_noncomm

/-! ## 2. Universal & Concrete `q`-Hecke Baxterized Spectral Yang–Baxter -/

/-- A pair of Artin-braid generators satisfying the quadratic Hecke relation in an algebra `A`. -/
structure HeckeGeneratorPair (A : Type*) [Ring A] [Algebra ℂ A] (q : ℂ) where
  T1 : A
  T2 : A
  artin : T1 * T2 * T1 = T2 * T1 * T2
  hecke1 : (T1 - algebraMap ℂ A q) * (T1 + algebraMap ℂ A q⁻¹) = 0
  hecke2 : (T2 - algebraMap ℂ A q) * (T2 + algebraMap ℂ A q⁻¹) = 0

/-- Baxterized spectral R-operator `R(x) = x T - x⁻¹ (T - (q - q⁻¹) • 1)`. -/
def baxterize {A : Type*} [Ring A] [Algebra ℂ A] (T : A) (q x : ℂ) : A :=
  x • T - x⁻¹ • (T - (q - q⁻¹) • (1 : A))

theorem baxterize_expand {A : Type*} [Ring A] [Algebra ℂ A] (T : A) (q x : ℂ) :
    baxterize T q x = (x - x⁻¹) • T + (x⁻¹ * (q - q⁻¹)) • (1 : A) := by
  unfold baxterize
  simp only [sub_smul, smul_sub, mul_sub, smul_smul, add_smul]
  abel

theorem hecke_sq_eq {A : Type*} [Ring A] [Algebra ℂ A] {T : A} {q : ℂ} (hq : q ≠ 0)
    (hH : (T - algebraMap ℂ A q) * (T + algebraMap ℂ A q⁻¹) = 0) :
    T * T = (q - q⁻¹) • T + 1 := by
  have h1 : (T - q • (1 : A)) * (T + q⁻¹ • (1 : A)) = 0 := by
    simpa [Algebra.algebraMap_eq_smul_one] using hH
  have hprod : (T - q • (1 : A)) * (T + q⁻¹ • (1 : A)) =
      T * T - (q - q⁻¹) • T - 1 := by
    rw [sub_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      smul_smul, one_mul, mul_one, mul_inv_cancel₀ hq, one_smul, mul_one, sub_smul]
    abel
  rw [hprod] at h1
  exact eq_add_of_sub_eq' (sub_eq_zero.mp h1)

private theorem baxterize_coeff_one (q x y : ℂ) (hq : q ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    let d := q - q⁻¹
    let ax := x - x⁻¹
    let bx := x⁻¹ * d
    let ay := y - y⁻¹
    let by_ := y⁻¹ * d
    let az := x * y - (x * y)⁻¹
    let bz := (x * y)⁻¹ * d
    ay * (bz * ax) * d + ay * (bz * bx) + by_ * (bz * ax) = by_ * (az * bx) := by
  intro d ax bx ay by_ az bz
  dsimp [ax, bx, ay, by_, az, bz, d]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  field_simp [hq, hx, hy, hxy]
  ring

private theorem baxterize_coeff_two (q x y : ℂ) (hq : q ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    let d := q - q⁻¹
    let ax := x - x⁻¹
    let bx := x⁻¹ * d
    let ay := y - y⁻¹
    let by_ := y⁻¹ * d
    let az := x * y - (x * y)⁻¹
    let bz := (x * y)⁻¹ * d
    by_ * (az * bx) = ax * (bz * ay) * d + ax * (bz * by_) + bx * (bz * ay) := by
  intro d ax bx ay by_ az bz
  dsimp [ax, bx, ay, by_, az, bz, d]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  field_simp [hq, hx, hy, hxy]
  ring

private theorem baxterize_coeff_zero (q x y : ℂ) :
    let d := q - q⁻¹
    let ax := x - x⁻¹
    let bx := x⁻¹ * d
    let ay := y - y⁻¹
    let by_ := y⁻¹ * d
    let bz := (x * y)⁻¹ * d
    by_ * (bz * bx) + ay * (bz * ax) = bx * (bz * by_) + ax * (bz * ay) := by
  intro d ax bx ay by_ bz; ring

private theorem baxterize_coeff_12 (q x y : ℂ) :
    let d := q - q⁻¹
    let ax := x - x⁻¹
    let by_ := y⁻¹ * d
    let az := x * y - (x * y)⁻¹
    by_ * (az * ax) = ax * (az * by_) := by
  intro d ax by_ az; ring

private theorem baxterize_coeff_21 (q x y : ℂ) :
    let d := q - q⁻¹
    let bx := x⁻¹ * d
    let ay := y - y⁻¹
    let az := x * y - (x * y)⁻¹
    ay * (az * bx) = bx * (az * ay) := by
  intro d bx ay az; ring

private theorem baxterize_coeff_121 (x y : ℂ) :
    let ax := x - x⁻¹
    let ay := y - y⁻¹
    let az := x * y - (x * y)⁻¹
    ay * (az * ax) = ax * (az * ay) := by
  intro ax ay az; ring

private theorem baxterize_linear_left {A : Type*} [Ring A] [Algebra ℂ A]
    (T1 T2 : A) (d ax bx az bz ay by_ : ℂ)
    (hT1sq : T1 * T1 = d • T1 + 1) :
    ((ax • T1 + bx • (1 : A)) * (az • T2 + bz • (1 : A))) * (ay • T1 + by_ • (1 : A)) =
      (by_ * (bz * bx) + ay * (bz * ax)) • (1 : A) +
      (ay * (bz * ax) * d + ay * (bz * bx) + by_ * (bz * ax)) • T1 +
      (by_ * (az * bx)) • T2 +
      (by_ * (az * ax)) • (T1 * T2) +
      (ay * (az * bx)) • (T2 * T1) +
      (ay * (az * ax)) • (T1 * T2 * T1) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_add, smul_smul]
  rw [hT1sq]
  simp only [smul_add, smul_smul, add_smul, ← mul_assoc]
  abel

private theorem baxterize_linear_right {A : Type*} [Ring A] [Algebra ℂ A]
    (T1 T2 : A) (d ax bx az bz ay by_ : ℂ)
    (hArtin : T1 * T2 * T1 = T2 * T1 * T2)
    (hT2sq : T2 * T2 = d • T2 + 1) :
    ((ay • T2 + by_ • (1 : A)) * (az • T1 + bz • (1 : A))) * (ax • T2 + bx • (1 : A)) =
      (bx * (bz * by_) + ax * (bz * ay)) • (1 : A) +
      (by_ * (az * bx)) • T1 +
      (ax * (bz * ay) * d + ax * (bz * by_) + bx * (bz * ay)) • T2 +
      (by_ * (az * ax)) • (T1 * T2) +
      (ay * (az * bx)) • (T2 * T1) +
      (ay * (az * ax)) • (T1 * T2 * T1) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_add, smul_smul]
  simp only [mul_assoc]
  rw [show T2 * (T1 * T2) = T1 * T2 * T1 from by rw [hArtin, mul_assoc]]
  rw [hT2sq]
  simp only [smul_add, smul_smul, add_smul, ← mul_assoc]
  rw [show ax * az * ay = ay * az * ax from by ring,
      show ax * az * by_ = by_ * az * ax from by ring,
      show bx * az * ay = ay * az * bx from by ring,
      show bx * az * by_ = by_ * az * bx from by ring]
  abel

/-- Universal associative-algebra Baxterized spectral Yang–Baxter equation. -/
theorem baxterized_yang_baxter {A : Type*} [Ring A] [Algebra ℂ A] {q : ℂ} (hq : q ≠ 0)
    (H : HeckeGeneratorPair A q) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    baxterize H.T1 q x * baxterize H.T2 q (x * y) * baxterize H.T1 q y =
      baxterize H.T2 q y * baxterize H.T1 q (x * y) * baxterize H.T2 q x := by
  have hT1sq : H.T1 * H.T1 = (q - q⁻¹) • H.T1 + 1 := hecke_sq_eq hq H.hecke1
  have hT2sq : H.T2 * H.T2 = (q - q⁻¹) • H.T2 + 1 := hecke_sq_eq hq H.hecke2
  simp only [baxterize_expand]
  rw [baxterize_linear_left H.T1 H.T2 (q - q⁻¹) (x - x⁻¹) (x⁻¹ * (q - q⁻¹))
    (x * y - (x * y)⁻¹) ((x * y)⁻¹ * (q - q⁻¹)) (y - y⁻¹) (y⁻¹ * (q - q⁻¹)) hT1sq]
  rw [baxterize_linear_right H.T1 H.T2 (q - q⁻¹) (x - x⁻¹) (x⁻¹ * (q - q⁻¹))
    (x * y - (x * y)⁻¹) ((x * y)⁻¹ * (q - q⁻¹)) (y - y⁻¹) (y⁻¹ * (q - q⁻¹)) H.artin hT2sq]
  rw [baxterize_coeff_zero q x y, baxterize_coeff_one q x y hq hx hy,
    baxterize_coeff_two q x y hq hx hy]

/-- Topological category (`TopCat`) Baxterized YBE via `HeckeBraidTopologicalBridge.leftMulTopCatHom`. -/
theorem hecke_baxterized_leftTopCat_ybe {R : Type*} [Ring R] [Algebra ℂ R]
    [TopologicalSpace R] [ContinuousMul R] {q : ℂ} (hq : q ≠ 0)
    (H : HeckeGeneratorPair R q) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    leftMulTopCatHom (baxterize H.T1 q y) ≫
        leftMulTopCatHom (baxterize H.T2 q (x * y)) ≫
        leftMulTopCatHom (baxterize H.T1 q x) =
      leftMulTopCatHom (baxterize H.T2 q x) ≫
        leftMulTopCatHom (baxterize H.T1 q (x * y)) ≫
        leftMulTopCatHom (baxterize H.T2 q y) := by
  rw [leftMulTopCatHom_comp, leftMulTopCatHom_comp, leftMulTopCatHom_comp, leftMulTopCatHom_comp]
  rw [baxterized_yang_baxter hq H hx hy]

/-- Jimbo's `4 × 4` `q`-Hecke check R-matrix on `ℂ² ⊗ ℂ²`. -/
def checkR (q : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![q, 0, 0, 0;
     0, q - q⁻¹, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, q]

theorem checkR_hecke (q : ℂ) (hq : q ≠ 0) :
    (checkR q - algebraMap ℂ (Matrix (Fin 4) (Fin 4) ℂ) q) *
      (checkR q + algebraMap ℂ (Matrix (Fin 4) (Fin 4) ℂ) q⁻¹) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [checkR, Algebra.algebraMap_eq_smul_one, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [hq] <;> ring

/-- At `q = 1`, `checkR 1` is the bosonic symmetric swap matrix. -/
theorem checkR_one :
    checkR 1 = !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [checkR]

/-- At `q = -1`, `checkR (-1)` is the fermionic signed swap matrix `diag(-1, 1, 1, -1) * P_swap`. -/
theorem checkR_neg_one :
    checkR (-1) = !![-1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [checkR]

/-- Diagonal `4 × 4` weight matrix used for the `Fin 4` T16 witness. -/
def diag4Weights : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 3, 0; 0, 0, 0, 4]

/-- Concrete `4 × 4` bosonic swap instance `checkR 1` for T16 witness matching. -/
def checkR1_4 : Matrix (Fin 4) (Fin 4) ℂ := checkR 1

/-- Binder-free T16 non-commutativity witness for `Matrix (Fin 4) (Fin 4) ℂ`. -/
theorem checkR1_4_noncomm_diag4Weights :
    checkR1_4 * diag4Weights ≠ diag4Weights * checkR1_4 := by
  intro h
  have h12 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 1 2) h
  simp [checkR1_4, checkR, diag4Weights, Matrix.mul_apply, Fin.sum_univ_four] at h12

/-- Embedding `A ⊗ I₂` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def kron42 (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if i.val % 2 = j.val % 2 then A ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ else 0

/-- Embedding `I₂ ⊗ A` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def kron24 (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if i.val / 4 = j.val / 4 then A ⟨i.val % 4, by omega⟩ ⟨j.val % 4, by omega⟩ else 0

/-- Explicit `8 × 8` Hecke generator `T₁(q) = checkR(q) ⊗ I₂`. -/
def heckeT1 (q : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let d := q - q⁻¹
  !![q, 0, 0, 0, 0, 0, 0, 0;
     0, q, 0, 0, 0, 0, 0, 0;
     0, 0, d, 0, 1, 0, 0, 0;
     0, 0, 0, d, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, q, 0;
     0, 0, 0, 0, 0, 0, 0, q]

/-- Explicit `8 × 8` Hecke generator `T₂(q) = I₂ ⊗ checkR(q)`. -/
def heckeT2 (q : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let d := q - q⁻¹
  !![q, 0, 0, 0, 0, 0, 0, 0;
     0, d, 1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, q, 0, 0, 0, 0;
     0, 0, 0, 0, q, 0, 0, 0;
     0, 0, 0, 0, 0, d, 1, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, q]

theorem heckeT1_eq_kron42 (q : ℂ) : heckeT1 q = kron42 (checkR q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeT1, kron42, checkR]

theorem heckeT2_eq_kron24 (q : ℂ) : heckeT2 q = kron24 (checkR q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeT2, kron24, checkR]

theorem heckeT1_hecke (q : ℂ) (hq : q ≠ 0) :
    (heckeT1 q - algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ) q) *
      (heckeT1 q + algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ) q⁻¹) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeT1, Algebra.algebraMap_eq_smul_one, Matrix.mul_apply, Fin.sum_univ_eight] <;>
    field_simp [hq] <;> ring

theorem heckeT2_hecke (q : ℂ) (hq : q ≠ 0) :
    (heckeT2 q - algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ) q) *
      (heckeT2 q + algebraMap ℂ (Matrix (Fin 8) (Fin 8) ℂ) q⁻¹) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeT2, Algebra.algebraMap_eq_smul_one, Matrix.mul_apply, Fin.sum_univ_eight] <;>
    field_simp [hq] <;> ring

private def heckeT12_mat (q : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let d := q - q⁻¹
  !![q ^ 2, 0, 0, 0, 0, 0, 0, 0;
     0, q * d, q, 0, 0, 0, 0, 0;
     0, d, 0, 0, q, 0, 0, 0;
     0, 0, 0, d * q, 0, d, 1, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, q, 0, 0, 0, 0;
     0, 0, 0, 0, 0, q, 0, 0;
     0, 0, 0, 0, 0, 0, 0, q ^ 2]

private def heckeT21_mat (q : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let d := q - q⁻¹
  !![q ^ 2, 0, 0, 0, 0, 0, 0, 0;
     0, q * d, d, 0, 1, 0, 0, 0;
     0, q, 0, 0, 0, 0, 0, 0;
     0, 0, 0, q * d, 0, q, 0, 0;
     0, 0, q, 0, 0, 0, 0, 0;
     0, 0, 0, d, 0, 0, q, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, q ^ 2]

private theorem heckeT1_mul_heckeT2 (q : ℂ) : heckeT1 q * heckeT2 q = heckeT12_mat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeT1, heckeT2, heckeT12_mat, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring

private theorem heckeT2_mul_heckeT1 (q : ℂ) : heckeT2 q * heckeT1 q = heckeT21_mat q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeT1, heckeT2, heckeT21_mat, Matrix.mul_apply, Fin.sum_univ_eight] <;> ring

set_option maxHeartbeats 800000 in
theorem heckeT1_heckeT2_artin (q : ℂ) :
    heckeT1 q * heckeT2 q * heckeT1 q = heckeT2 q * heckeT1 q * heckeT2 q := by
  rw [heckeT1_mul_heckeT2, heckeT2_mul_heckeT1]
  by_cases hq : q = 0
  · subst hq
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeT12_mat, heckeT21_mat, heckeT1, heckeT2, Matrix.mul_apply, Fin.sum_univ_eight]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeT12_mat, heckeT21_mat, heckeT1, heckeT2, Matrix.mul_apply,
        Fin.sum_univ_eight] <;>
      field_simp [hq] <;> ring

/-- Concrete `8 × 8` `HeckeGeneratorPair` for any nonzero `q : ℂ`. -/
def concreteHeckePair (q : ℂ) (hq : q ≠ 0) :
    HeckeGeneratorPair (Matrix (Fin 8) (Fin 8) ℂ) q where
  T1 := heckeT1 q
  T2 := heckeT2 q
  artin := heckeT1_heckeT2_artin q
  hecke1 := heckeT1_hecke q hq
  hecke2 := heckeT2_hecke q hq

/-- Binder-free T17 constructive inhabitant at the Fibonacci root `YangBaxterProof.q`. -/
def fibonacciHeckePair :
    HeckeGeneratorPair (Matrix (Fin 8) (Fin 8) ℂ) InfoGeometry.Canonical.YangBaxterProof.q :=
  concreteHeckePair InfoGeometry.Canonical.YangBaxterProof.q (Complex.exp_ne_zero _)

instance :
    Inhabited (HeckeGeneratorPair (Matrix (Fin 8) (Fin 8) ℂ)
      InfoGeometry.Canonical.YangBaxterProof.q) :=
  ⟨fibonacciHeckePair⟩

/-- Concrete `8 × 8` Baxterized spectral Yang–Baxter theorem for `heckeT1 q`, `heckeT2 q`. -/
theorem hecke_8x8_baxterized_ybe {q x y : ℂ} (hq : q ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    baxterize (heckeT1 q) q x * baxterize (heckeT2 q) q (x * y) * baxterize (heckeT1 q) q y =
      baxterize (heckeT2 q) q y * baxterize (heckeT1 q) q (x * y) * baxterize (heckeT2 q) q x :=
  baxterized_yang_baxter hq (concreteHeckePair q hq) hx hy

/-- Spectral `R`-matrix `R₁₂(z; q) = P₁₂ * baxterize (heckeT1 q) q z` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def heckeSpecR12 (q z : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  P12 * baxterize (heckeT1 q) q z

/-- Spectral `R`-matrix `R₂₃(y; q) = P₂₃ * baxterize (heckeT2 q) q y` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def heckeSpecR23 (q y : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  P23 * baxterize (heckeT2 q) q y

/-- Spectral `R`-matrix `R₁₃(z; q) = P₁₂ * R₂₃(z; q) * P₁₂` on `Matrix (Fin 8) (Fin 8) ℂ`. -/
def heckeSpecR13 (q z : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  P12 * heckeSpecR23 q z * P12

private theorem swap23_comp_swap12_val :
    ∀ i : Fin 8, (swap23 ∘ swap12) i = ![0, 2, 4, 6, 1, 3, 5, 7] i := by
  intro i; fin_cases i <;> decide

private theorem swap12_comp_swap23_val :
    ∀ i : Fin 8, (swap12 ∘ swap23) i = ![0, 4, 1, 5, 2, 6, 3, 7] i := by
  intro i; fin_cases i <;> decide

private theorem swap23_comp_swap12_iff (k j : Fin 8) :
    (swap23 ∘ swap12) k = j ↔ k = (swap12 ∘ swap23) j := by
  fin_cases k <;> fin_cases j <;> decide

private theorem swap12_comp_swap23_iff (k j : Fin 8) :
    (swap12 ∘ swap23) k = j ↔ k = (swap23 ∘ swap12) j := by
  fin_cases k <;> fin_cases j <;> decide

private theorem cycle123_conj_T1 (q : ℂ) :
    (P12 * P23) * heckeT1 q = heckeT2 q * (P12 * P23) := by
  have h1 : P12 * P23 = swapMat (swap23 ∘ swap12) := by rw [P12, P23, swapMat_mul]
  rw [h1, swapMat_mul_left, mul_swapMat_right (heckeT2 q) (swap23 ∘ swap12) (swap12 ∘ swap23)
    swap23_comp_swap12_iff]
  ext i j
  simp only [Matrix.of_apply, swap23_comp_swap12_val, swap12_comp_swap23_val]
  fin_cases i <;> fin_cases j <;> simp [heckeT1, heckeT2]

private theorem cycle132_conj_T2 (q : ℂ) :
    (P23 * P12) * heckeT2 q = heckeT1 q * (P23 * P12) := by
  have h1 : P23 * P12 = swapMat (swap12 ∘ swap23) := by rw [P23, P12, swapMat_mul]
  rw [h1, swapMat_mul_left, mul_swapMat_right (heckeT1 q) (swap12 ∘ swap23) (swap23 ∘ swap12)
    swap12_comp_swap23_iff]
  ext i j
  simp only [Matrix.of_apply, swap12_comp_swap23_val, swap23_comp_swap12_val]
  fin_cases i <;> fin_cases j <;> simp [heckeT1, heckeT2]

private theorem cycle123_conj_bax (q x : ℂ) :
    (P12 * P23) * baxterize (heckeT1 q) q x = baxterize (heckeT2 q) q x * (P12 * P23) := by
  simp only [baxterize_expand, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  rw [cycle123_conj_T1]

private theorem cycle132_conj_bax (q x : ℂ) :
    (P23 * P12) * baxterize (heckeT2 q) q x = baxterize (heckeT1 q) q x * (P23 * P12) := by
  simp only [baxterize_expand, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  rw [cycle132_conj_T2]

private theorem cycle123_sq : (P12 * P23) * (P12 * P23) = P23 * P12 := by
  rw [← Matrix.mul_assoc, show P12 * P23 * P12 = P13 from P13_eq_P12_P23_P12.symm,
    P13_eq_P23_P12_P23, Matrix.mul_assoc, P23_sq, mul_one]

private theorem cycle123_mul_cycle132 : (P12 * P23) * (P23 * P12) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc P23 P23 P12, P23_sq, one_mul, P12_sq]

private theorem cycle132_mul_cycle123 : (P23 * P12) * (P12 * P23) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc P12 P12 P23, P12_sq, one_mul, P23_sq]

/-- Concrete `8 × 8` `q`-Hecke Baxterized spectral Yang–Baxter equation:
    `R₁₂(z / y) * R₁₃(z) * R₂₃(y) = R₂₃(y) * R₁₃(z) * R₁₂(z / y)`. -/
theorem hecke_8x8_spectral_yang_baxter {q y z : ℂ} (hq : q ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    heckeSpecR12 q (z / y) * heckeSpecR13 q z * heckeSpecR23 q y =
      heckeSpecR23 q y * heckeSpecR13 q z * heckeSpecR12 q (z / y) := by
  set x := z / y
  have hx : x ≠ 0 := div_ne_zero hz hy
  have hyx : y * x = z := mul_div_cancel₀ z hy
  have hL : P13 * (heckeSpecR12 q x * heckeSpecR13 q z * heckeSpecR23 q y) =
      baxterize (heckeT2 q) q x * baxterize (heckeT1 q) q (y * x) * baxterize (heckeT2 q) q y := by
    rw [hyx]
    unfold heckeSpecR12 heckeSpecR13 heckeSpecR23
    calc
      P13 * (P12 * baxterize (heckeT1 q) q x * (P12 * (P23 * baxterize (heckeT2 q) q z) * P12) *
          (P23 * baxterize (heckeT2 q) q y))
          = (P12 * P23) * baxterize (heckeT1 q) q x *
              ((P12 * P23) * baxterize (heckeT2 q) q z * (P12 * P23)) *
              baxterize (heckeT2 q) q y := by
            rw [P13_eq_P12_P23_P12]
            simp only [Matrix.mul_assoc]
            congr 2
            rw [← Matrix.mul_assoc P12 P12 _, P12_sq, one_mul]
      _ = baxterize (heckeT2 q) q x * ((P12 * P23) * (P12 * P23)) *
            baxterize (heckeT2 q) q z * (P12 * P23) * baxterize (heckeT2 q) q y := by
            rw [cycle123_conj_bax]
            simp only [Matrix.mul_assoc]
      _ = baxterize (heckeT2 q) q x * ((P23 * P12) * baxterize (heckeT2 q) q z) *
            (P12 * P23) * baxterize (heckeT2 q) q y := by
            rw [cycle123_sq]
            simp only [Matrix.mul_assoc]
      _ = baxterize (heckeT2 q) q x * baxterize (heckeT1 q) q z *
            ((P23 * P12) * (P12 * P23)) * baxterize (heckeT2 q) q y := by
            rw [cycle132_conj_bax]
            simp only [Matrix.mul_assoc]
      _ = baxterize (heckeT2 q) q x * baxterize (heckeT1 q) q z * baxterize (heckeT2 q) q y := by
            rw [cycle132_mul_cycle123, mul_one]
  have hR : P13 * (heckeSpecR23 q y * heckeSpecR13 q z * heckeSpecR12 q x) =
      baxterize (heckeT1 q) q y * baxterize (heckeT2 q) q (y * x) * baxterize (heckeT1 q) q x := by
    rw [hyx]
    unfold heckeSpecR12 heckeSpecR13 heckeSpecR23
    calc
      P13 * (P23 * baxterize (heckeT2 q) q y * (P12 * (P23 * baxterize (heckeT2 q) q z) * P12) *
          (P12 * baxterize (heckeT1 q) q x))
          = (P23 * P12) * (P23 * P23) * baxterize (heckeT2 q) q y * P12 * P23 *
              baxterize (heckeT2 q) q z * (P12 * P12) * baxterize (heckeT1 q) q x := by
            rw [P13_eq_P23_P12_P23]
            simp only [Matrix.mul_assoc]
      _ = (P23 * P12) * baxterize (heckeT2 q) q y *
              ((P12 * P23) * baxterize (heckeT2 q) q z) * baxterize (heckeT1 q) q x := by
            rw [P23_sq, P12_sq, mul_one, mul_one]
            simp only [Matrix.mul_assoc]
      _ = baxterize (heckeT1 q) q y * ((P23 * P12) * (P12 * P23)) *
            baxterize (heckeT2 q) q z * baxterize (heckeT1 q) q x := by
            rw [cycle132_conj_bax]
            simp only [Matrix.mul_assoc]
      _ = baxterize (heckeT1 q) q y * baxterize (heckeT2 q) q z * baxterize (heckeT1 q) q x := by
            rw [cycle132_mul_cycle123, mul_one]
  have hmid : P13 * (heckeSpecR12 q x * heckeSpecR13 q z * heckeSpecR23 q y) =
      P13 * (heckeSpecR23 q y * heckeSpecR13 q z * heckeSpecR12 q x) := by
    rw [hL, hR]
    exact (hecke_8x8_baxterized_ybe hq hy hx).symm
  have hfin := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℂ => P13 * M) hmid
  simpa only [← Matrix.mul_assoc, P13_sq, one_mul] using hfin

/-! ## 3. `q`-Parameterized `B_n` and `B_∞` Representation & CAR/CCR Collapse -/

/-- Infinite-mode Fock configuration space `(ℕ → Bool) → ℂ` (extending `BosonFermionRegression`). -/
abbrev FockConfigSpace := (ℕ → Bool) → ℂ

/-- Adjacent `q`-anyonic mode exchange linear map on `FockConfigSpace`.
    Multiplies doubly occupied adjacent sites `(s i && s (i+1))` by `q` and swaps modes `i ↔ i+1`. -/
def qSwapLinearMap (q : ℂ) (i : ℕ) : FockConfigSpace →ₗ[ℂ] FockConfigSpace where
  toFun f s := (if s i && s (i + 1) then q else 1) * f (s ∘ Equiv.swap i (i + 1))
  map_add' f g := by funext s; simp [mul_add]
  map_smul' c f := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem qSwap_both_swap (s : ℕ → Bool) (i : ℕ) :
    (s (Equiv.swap i (i + 1) i) && s (Equiv.swap i (i + 1) (i + 1))) = (s i && s (i + 1)) := by
  simp [Equiv.swap_apply_left, Equiv.swap_apply_right, Bool.and_comm]

/-- Invertible linear equivalence realizing generator `σᵢ` at parameter `q ≠ 0`. -/
def qSwapEquiv (q : ℂ) (hq : q ≠ 0) (i : ℕ) : FockConfigSpace ≃ₗ[ℂ] FockConfigSpace where
  toLinearMap := qSwapLinearMap q i
  invFun f s := (if s i && s (i + 1) then q⁻¹ else 1) * f (s ∘ Equiv.swap i (i + 1))
  left_inv f := by
    funext s
    have hinv : (s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap i (i + 1) = s := by
      funext k; simp [Function.comp_apply]
    simp only [qSwapLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    change (if s i && s (i + 1) then q⁻¹ else 1) *
        ((if (s ∘ Equiv.swap i (i + 1)) i && (s ∘ Equiv.swap i (i + 1)) (i + 1) then q else 1) *
          f ((s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap i (i + 1))) = f s
    rw [hinv, show ((s ∘ Equiv.swap i (i + 1)) i && (s ∘ Equiv.swap i (i + 1)) (i + 1)) =
      (s i && s (i + 1)) from by simpa [Function.comp_apply] using qSwap_both_swap s i]
    by_cases h : s i && s (i + 1)
    · simp [h, ← mul_assoc, inv_mul_cancel₀ hq]
    · simp [h]
  right_inv f := by
    funext s
    have hinv : (s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap i (i + 1) = s := by
      funext k; simp [Function.comp_apply]
    simp only [qSwapLinearMap, LinearMap.coe_mk]
    change (if s i && s (i + 1) then q else 1) *
        ((if (s ∘ Equiv.swap i (i + 1)) i && (s ∘ Equiv.swap i (i + 1)) (i + 1) then q⁻¹ else 1) *
          f ((s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap i (i + 1))) = f s
    rw [hinv, show ((s ∘ Equiv.swap i (i + 1)) i && (s ∘ Equiv.swap i (i + 1)) (i + 1)) =
      (s i && s (i + 1)) from by simpa [Function.comp_apply] using qSwap_both_swap s i]
    by_cases h : s i && s (i + 1)
    · simp [h, ← mul_assoc, mul_inv_cancel₀ hq]
    · simp [h]

@[simp]
theorem qSwapEquiv_apply (q : ℂ) (hq : q ≠ 0) (i : ℕ) (f : FockConfigSpace) (s : ℕ → Bool) :
    qSwapEquiv q hq i f s = (if s i && s (i + 1) then q else 1) * f (s ∘ Equiv.swap i (i + 1)) :=
  rfl

/-- Adjacent Artin braid relation for `qSwapEquiv q hq`. -/
theorem qSwapEquiv_artin (q : ℂ) (hq : q ≠ 0) (i : ℕ) :
    qSwapEquiv q hq i * qSwapEquiv q hq (i + 1) * qSwapEquiv q hq i =
      qSwapEquiv q hq (i + 1) * qSwapEquiv q hq i * qSwapEquiv q hq (i + 1) := by
  ext f s
  have hL :
      Equiv.swap i (i + 1) i = i + 1 ∧
      Equiv.swap i (i + 1) (i + 1) = i ∧
      Equiv.swap i (i + 1) (i + 1 + 1) = i + 1 + 1 ∧
      Equiv.swap (i + 1) (i + 1 + 1) i = i ∧
      Equiv.swap (i + 1) (i + 1 + 1) (i + 1) = i + 1 + 1 ∧
      Equiv.swap (i + 1) (i + 1 + 1) (i + 1 + 1) = i + 1 := by
    refine ⟨Equiv.swap_apply_left _ _, Equiv.swap_apply_right _ _,
      Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
      Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
      Equiv.swap_apply_left _ _, Equiv.swap_apply_right _ _⟩
  have hperm :
      ((s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap (i + 1) (i + 1 + 1)) ∘ Equiv.swap i (i + 1) =
        ((s ∘ Equiv.swap (i + 1) (i + 1 + 1)) ∘ Equiv.swap i (i + 1)) ∘
          Equiv.swap (i + 1) (i + 1 + 1) := by
    funext k
    simp only [Function.comp_apply]
    by_cases hk0 : k = i
    · simp only [hk0, hL]
    · by_cases hk1 : k = i + 1
      · simp only [hk1, hL]
      · by_cases hk2 : k = i + 1 + 1
        · simp only [hk2, hL]
        · simp [Equiv.swap_apply_of_ne_of_ne hk0 hk1,
            Equiv.swap_apply_of_ne_of_ne hk1 hk2]
  simp only [LinearEquiv.mul_apply, qSwapEquiv_apply, Function.comp_apply,
    hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, hL.2.2.2.2.1, hL.2.2.2.2.2]
  rw [congrArg f hperm]
  cases s i <;> cases s (i + 1) <;> cases s (i + 1 + 1) <;> simp <;> ring

/-- Far commutation relation for `qSwapEquiv q hq` when `i + 2 ≤ j`. -/
theorem qSwapEquiv_far (q : ℂ) (hq : q ≠ 0) (i j : ℕ) (hij : i + 2 ≤ j) :
    qSwapEquiv q hq i * qSwapEquiv q hq j = qSwapEquiv q hq j * qSwapEquiv q hq i := by
  ext f s
  have hdisj1 : Equiv.swap i (i + 1) j = j :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hdisj2 : Equiv.swap i (i + 1) (j + 1) = j + 1 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hdisj3 : Equiv.swap j (j + 1) i = i :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hdisj4 : Equiv.swap j (j + 1) (i + 1) = i + 1 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hperm : (s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap j (j + 1) =
      (s ∘ Equiv.swap j (j + 1)) ∘ Equiv.swap i (i + 1) := by
    funext k
    simp only [Function.comp_apply]
    by_cases hk1 : k = i
    · simp only [hk1, Equiv.swap_apply_left, hdisj3, hdisj4, Equiv.swap_apply_right]
    · by_cases hk2 : k = i + 1
      · simp only [hk2, Equiv.swap_apply_right, hdisj4, hdisj3, Equiv.swap_apply_left]
      · by_cases hk3 : k = j
        · simp only [hk3, hdisj1, Equiv.swap_apply_left, Equiv.swap_apply_right, hdisj2]
        · by_cases hk4 : k = j + 1
          · simp only [hk4, hdisj2, Equiv.swap_apply_right, Equiv.swap_apply_left, hdisj1]
          · simp [Equiv.swap_apply_of_ne_of_ne hk1 hk2, Equiv.swap_apply_of_ne_of_ne hk3 hk4]
  simp only [LinearEquiv.mul_apply, qSwapEquiv_apply, Function.comp_apply,
    hdisj1, hdisj2, hdisj3, hdisj4]
  rw [congrArg f hperm]
  ring

/-- Finite-stage `ArtinBraidSystem` for `B_{m+1}` acting on `FockConfigSpace`. -/
def finiteBraidArtinSystem (m : ℕ) (q : ℂ) (hq : q ≠ 0) :
    ArtinBraidSystem (FockConfigSpace ≃ₗ[ℂ] FockConfigSpace) m where
  gen i := qSwapEquiv q hq i.val
  adjacent i j hij := by
    have hj : j.val = i.val + 1 := hij.symm
    rw [hj]
    exact qSwapEquiv_artin q hq i.val
  farCommute i j hij := qSwapEquiv_far q hq i.val j.val hij

/-- Finite-stage `B_{m+1}` linear-equivalence representation on `FockConfigSpace`. -/
def braidInterpFinite (m : ℕ) (q : ℂ) (hq : q ≠ 0) :
    braid_group (m + 1) →* (FockConfigSpace ≃ₗ[ℂ] FockConfigSpace) :=
  (finiteBraidArtinSystem m q hq).toGroupHom

/-- Relator preservation for the infinite braid group `B_∞`. -/
theorem qSwapEquiv_inf_rels (q : ℂ) (hq : q ≠ 0) :
    ∀ r ∈ braid_rels_inf, FreeGroup.lift (qSwapEquiv q hq) r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · have hArt := qSwapEquiv_artin q hq i
    simpa [Braid.braid_rel, FreeGroup.lift_apply_of, mul_assoc] using
      freeGroup_lift_braid_relator (qSwapEquiv q hq) i (i + 1) hArt
  · have hComm := qSwapEquiv_far q hq i j hij
    simpa [Braid.comm_rel, FreeGroup.lift_apply_of, mul_assoc] using
      freeGroup_lift_comm_relator (qSwapEquiv q hq) i j hComm

/-- Genuine axiom-free representation of the infinite braid group `B_∞` on `FockConfigSpace`. -/
def braidInterpInf (q : ℂ) (hq : q ≠ 0) :
    braid_group_inf →* (FockConfigSpace ≃ₗ[ℂ] FockConfigSpace) :=
  braid_group_inf.toGroup (qSwapEquiv q hq) (qSwapEquiv_inf_rels q hq)

/-- Compatibility with the canonical finite-to-infinite braid colimit embedding. -/
theorem braidInterpInf_comp_finite (m : ℕ) (q : ℂ) (hq : q ≠ 0) :
    (braidInterpInf q hq).comp (finiteToInfiniteGroupHom m) = braidInterpFinite m q hq := by
  apply (finiteBraidArtinSystem m q hq).toGroupHom_unique
  intro i
  change braidInterpInf q hq (finiteToInfiniteGroupHom m (σ' m i)) = qSwapEquiv q hq i.val
  rw [finiteToInfiniteGroupHom_sigma, braidInterpInf, braid_group_inf.toGroup_sigma]

/-- Bosonic CCR symmetric mode-swap operator (`q = 1`). -/
def bosonicSwap (i : ℕ) : FockConfigSpace ≃ₗ[ℂ] FockConfigSpace :=
  qSwapEquiv 1 one_ne_zero i

/-- Fermionic CAR signed mode-swap operator (`q = -1`). -/
def fermionicSwap (i : ℕ) : FockConfigSpace ≃ₗ[ℂ] FockConfigSpace :=
  qSwapEquiv (-1) (by norm_num) i

theorem bosonicSwap_apply (i : ℕ) (f : FockConfigSpace) (s : ℕ → Bool) :
    bosonicSwap i f s = f (s ∘ Equiv.swap i (i + 1)) := by
  simp [bosonicSwap]

theorem fermionicSwap_apply (i : ℕ) (f : FockConfigSpace) (s : ℕ → Bool) :
    fermionicSwap i f s =
      (if s i && s (i + 1) then -1 else 1) * f (s ∘ Equiv.swap i (i + 1)) :=
  rfl

theorem bosonicSwap_sq (i : ℕ) : bosonicSwap i * bosonicSwap i = 1 := by
  ext f s
  simp only [LinearEquiv.mul_apply, bosonicSwap_apply]
  have hcomp : (s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap i (i + 1) = s := by
    funext x; simp
  rw [hcomp]
  rfl

theorem fermionicSwap_sq (i : ℕ) : fermionicSwap i * fermionicSwap i = 1 := by
  ext f s
  have hcomp : (s ∘ Equiv.swap i (i + 1)) ∘ Equiv.swap i (i + 1) = s := by
    funext x; simp
  have hbool : ((s ∘ Equiv.swap i (i + 1)) i && (s ∘ Equiv.swap i (i + 1)) (i + 1)) =
      (s i && s (i + 1)) := by
    simp [Function.comp_apply, Bool.and_comm]
  change fermionicSwap i (fermionicSwap i f) s = f s
  rw [fermionicSwap_apply, fermionicSwap_apply, hbool, hcomp]
  by_cases h : s i && s (i + 1) <;> simp [h]

/-- On doubly occupied adjacent fermionic modes, `fermionicSwap` introduces a Koszul `-1` phase. -/
theorem fermionicSwap_antisymmetric_occupied (i : ℕ) (f : FockConfigSpace) (s : ℕ → Bool)
    (hi : s i = true) (hi1 : s (i + 1) = true)
    (hsym : f (s ∘ Equiv.swap i (i + 1)) = f s) :
    fermionicSwap i f s = - f s := by
  simp [fermionicSwap_apply, hi, hi1, hsym]

/-- Collapse of the `q`-braid representation to the bosonic symmetric group action at `q = 1`. -/
theorem braid_collapse_to_boson (i : ℕ) :
    braidInterpInf 1 one_ne_zero (σi i) = bosonicSwap i := by
  exact braid_group_inf.toGroup_sigma _ _ i

/-- Collapse of the `q`-braid representation to the fermionic signed exchange at `q = -1`. -/
theorem braid_collapse_to_fermion (i : ℕ) :
    braidInterpInf (-1) (by norm_num) (σi i) = fermionicSwap i := by
  exact braid_group_inf.toGroup_sigma _ _ i

/-- Instantiation at the Fibonacci anyon root `YangBaxterProof.q = exp(iπ/5)`. -/
def fibonacciBraidInf : braid_group_inf →* (FockConfigSpace ≃ₗ[ℂ] FockConfigSpace) :=
  braidInterpInf InfoGeometry.Canonical.YangBaxterProof.q (Complex.exp_ne_zero _)

/-- Non-commutativity witness on `FockConfigSpace ≃ₗ[ℂ] FockConfigSpace`: `σ₀ * σ₁ ≠ σ₁ * σ₀`. -/
theorem bosonicSwap_zero_one_noncomm :
    bosonicSwap 0 * bosonicSwap 1 ≠ bosonicSwap 1 * bosonicSwap 0 := by
  intro h
  let f0 : FockConfigSpace := fun s => if s 0 then 1 else 0
  let s1 : ℕ → Bool := fun k => decide (k = 1)
  have hval := congrArg (fun E : FockConfigSpace ≃ₗ[ℂ] FockConfigSpace => E f0 s1) h
  simp only [LinearEquiv.mul_apply, bosonicSwap_apply, Function.comp_apply, f0, s1,
    Nat.zero_add, Nat.reduceAdd] at hval
  have hs1 : s1 ((Equiv.swap 0 1) ((Equiv.swap 1 2) 0)) = true := by decide
  have hs2 : s1 ((Equiv.swap 1 2) ((Equiv.swap 0 1) 0)) = false := by decide
  change (if s1 ((Equiv.swap 0 1) ((Equiv.swap 1 2) 0)) then (1 : ℂ) else 0) =
    if s1 ((Equiv.swap 1 2) ((Equiv.swap 0 1) 0)) then (1 : ℂ) else 0 at hval
  rw [hs1, hs2] at hval
  norm_num at hval

/-! ## 4. `q`-Bracket Interpolation to `QCCRResidual` & `CARBracket` / `CCRBracket` -/

/-- `q`-deformed commutator bracket `[A, B]_q = A ∘ B - q • (B ∘ A)` on `FockEndomorphism E`. -/
def qBracket {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (q : ℝ) (A B : FockEndomorphism E) : FockEndomorphism E :=
  A.comp B - q • (B.comp A)

theorem qBracket_one_eq_ccrBracket {E : Type 0} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (A B : FockEndomorphism E) :
    qBracket 1 A B = CCRBracket A B := by
  rw [qBracket, CCRBracket, InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator_eq, one_smul]

theorem qBracket_neg_one_eq_carBracket {E : Type 0} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (A B : FockEndomorphism E) :
    qBracket (-1) A B = CARBracket A B := by
  unfold qBracket CARBracket fockAnticommutator anticommutator
  rw [superBracket_odd_odd, neg_one_smul ℝ (B.comp A), sub_neg_eq_add]

/-- Compatibility with `QCCRResidual`: `qCcrRelation a astar 1 = 0` is CCR and `-1` is CAR. -/
theorem qccr_endpoint_interpolation {R : Type*} [Ring R] (a astar : R) :
    (qCcrRelation a astar 1 = 0 ↔ a * astar - astar * a = 1) ∧
      (qCcrRelation a astar (-1) = 0 ↔ a * astar + astar * a = 1) :=
  ⟨qccr_bosonic_limit a astar, qccr_fermionic_limit a astar⟩

end InfoGeometry.Quantum.BraidInterpolation

end noncomputable section

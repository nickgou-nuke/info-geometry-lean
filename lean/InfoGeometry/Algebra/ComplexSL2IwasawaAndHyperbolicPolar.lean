/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra.ComplexSL2IwasawaAndHyperbolicPolar

open Matrix
open scoped ComplexConjugate

lemma conj_mul_self_eq_normSq (z : ℂ) : conj z * z = (Complex.normSq z : ℂ) := by
  exact Complex.normSq_eq_conj_mul_self.symm

lemma mul_conj_self_eq_normSq (z : ℂ) : z * conj z = (Complex.normSq z : ℂ) := by
  rw [mul_comm]
  exact Complex.normSq_eq_conj_mul_self.symm

lemma conj_ofReal (r : ℝ) : conj (r : ℂ) = (r : ℂ) := by
  exact Complex.conj_ofReal r

private lemma star_eq_conj (z : ℂ) : star z = conj z := by
  apply Complex.ext <;> rfl

lemma sq_eq_sq_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 = y ^ 2) : x = y := by
  have : (x - y) * (x + y) = 0 := by
    calc (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    _ = 0 := by linarith [h]
  cases mul_eq_zero.mp this with
  | inl hsub => linarith
  | inr hadd => linarith [hx, hy, hadd]

lemma conj_div_ofReal (z : ℂ) (r : ℝ) :
    conj (z / (r : ℂ)) = conj z / (r : ℂ) := by
  rw [map_div₀, Complex.conj_ofReal]

lemma conj_neg_conj_div_ofReal (z : ℂ) (r : ℝ) :
    conj (- conj z / (r : ℂ)) = - z / (r : ℂ) := by
  rw [map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal]

lemma conj_conj_div_ofReal (z : ℂ) (r : ℝ) :
    conj (conj z / (r : ℂ)) = z / (r : ℂ) := by
  rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]

lemma conjTranspose_fin_two (a b c d : ℂ) :
    (!![a, b; c, d]ᴴ : Matrix (Fin 2) (Fin 2) ℂ) = !![conj a, conj c; conj b, conj d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma one_fin_two : (1 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma unitary_det_normSq_one (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    Complex.normSq U.det = 1 := by
  have h_det : (Uᴴ * U).det = 1 := by
    rw [hU, det_one]
  rw [det_mul, det_conjTranspose] at h_det
  change conj U.det * U.det = 1 at h_det
  rw [conj_mul_self_eq_normSq] at h_det
  exact_mod_cast h_det

lemma unitary_fin_two_entries (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    conj (U 0 0) * U 0 0 + conj (U 1 0) * U 1 0 = 1 ∧
    conj (U 0 0) * U 0 1 + conj (U 1 0) * U 1 1 = 0 := by
  have h00 : (Uᴴ * U) 0 0 = 1 := by
    rw [hU]
    rfl
  have h01 : (Uᴴ * U) 0 1 = 0 := by
    rw [hU]
    rfl
  have h_mul00 : (Uᴴ * U) 0 0 = conj (U 0 0) * U 0 0 + conj (U 1 0) * U 1 0 := by
    rw [mul_apply, Fin.sum_univ_two, conjTranspose_apply, conjTranspose_apply]
    rfl
  have h_mul01 : (Uᴴ * U) 0 1 = conj (U 0 0) * U 0 1 + conj (U 1 0) * U 1 1 := by
    rw [mul_apply, Fin.sum_univ_two, conjTranspose_apply, conjTranspose_apply]
    rfl
  rw [h_mul00] at h00
  rw [h_mul01] at h01
  exact ⟨h00, h01⟩

lemma k_mat_unitary (u v : ℂ) (r : ℝ) (hr : (r : ℂ) ^ 2 = conj u * u + conj v * v) (hr_ne : (r : ℂ) ^ 2 ≠ 0) :
    (!![u / (r : ℂ), - conj v / (r : ℂ); v / (r : ℂ), conj u / (r : ℂ)]ᴴ : Matrix (Fin 2) (Fin 2) ℂ) *
     !![u / (r : ℂ), - conj v / (r : ℂ); v / (r : ℂ), conj u / (r : ℂ)] = 1 := by
  rw [conjTranspose_fin_two, mul_fin_two, one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp
    rw [conj_div_ofReal, conj_div_ofReal]
    have h_alg : (conj u / (r : ℂ)) * (u / (r : ℂ)) + (conj v / (r : ℂ)) * (v / (r : ℂ)) =
        (conj u * u + conj v * v) / (r : ℂ) ^ 2 := by
      ring
    rw [h_alg, ← hr]
    exact div_self hr_ne
  · dsimp
    rw [conj_div_ofReal, conj_div_ofReal]
    ring
  · dsimp
    rw [conj_neg_conj_div_ofReal, conj_conj_div_ofReal]
    ring
  · dsimp
    rw [conj_neg_conj_div_ofReal, conj_conj_div_ofReal]
    have h_alg : (- v / (r : ℂ)) * (- conj v / (r : ℂ)) + (u / (r : ℂ)) * (conj u / (r : ℂ)) =
        (conj u * u + conj v * v) / (r : ℂ) ^ 2 := by
      ring
    rw [h_alg, ← hr]
    exact div_self hr_ne

lemma k_mat_det (u v : ℂ) (r : ℝ) (hr : (r : ℂ) ^ 2 = conj u * u + conj v * v) (hr_ne : (r : ℂ) ^ 2 ≠ 0) :
    (!![u / (r : ℂ), - conj v / (r : ℂ); v / (r : ℂ), conj u / (r : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [det_fin_two]
  dsimp
  have h_alg : (u / (r : ℂ)) * (conj u / (r : ℂ)) - (- conj v / (r : ℂ)) * (v / (r : ℂ)) =
      (conj u * u + conj v * v) / (r : ℂ) ^ 2 := by
    ring
  rw [h_alg, ← hr]
  exact div_self hr_ne

lemma det_diag_two (a b : ℂ) : (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℂ).det = a * b := by
  rw [det_fin_two]
  dsimp
  ring

lemma det_upper_tri_one (z : ℂ) : (!![(1 : ℂ), z; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [det_fin_two]
  dsimp
  ring

lemma k_gl2_unitary (u v ω : ℂ) (r : ℝ) (hω : conj ω * ω = 1)
    (hr : (r : ℂ) ^ 2 = conj u * u + conj v * v) (hr_ne : (r : ℂ) ^ 2 ≠ 0) :
    (!![u / (r : ℂ), - ω * conj v / (r : ℂ); v / (r : ℂ), ω * conj u / (r : ℂ)]ᴴ : Matrix (Fin 2) (Fin 2) ℂ) *
     !![u / (r : ℂ), - ω * conj v / (r : ℂ); v / (r : ℂ), ω * conj u / (r : ℂ)] = 1 := by
  rw [conjTranspose_fin_two, mul_fin_two, one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp
    rw [conj_div_ofReal, conj_div_ofReal]
    have h_alg : (conj u / (r : ℂ)) * (u / (r : ℂ)) + (conj v / (r : ℂ)) * (v / (r : ℂ)) =
        (conj u * u + conj v * v) / (r : ℂ) ^ 2 := by
      ring
    rw [h_alg, ← hr]
    exact div_self hr_ne
  · dsimp
    rw [conj_div_ofReal, conj_div_ofReal]
    ring
  · dsimp
    rw [conj_div_ofReal, conj_div_ofReal, map_mul, map_neg, map_mul, Complex.conj_conj, Complex.conj_conj]
    ring
  · dsimp
    rw [conj_div_ofReal, conj_div_ofReal, map_mul, map_neg, map_mul, Complex.conj_conj, Complex.conj_conj]
    have h_alg : (- conj ω * v / (r : ℂ)) * (- ω * conj v / (r : ℂ)) +
        ((conj ω * u) / (r : ℂ)) * ((ω * conj u) / (r : ℂ)) =
        (conj ω * ω) * ((conj u * u + conj v * v) / (r : ℂ) ^ 2) := by
      ring
    rw [h_alg, hω, one_mul, ← hr]
    exact div_self hr_ne

/-- Structure representing the Iwasawa K A N decomposition in SL(2, ℂ). -/
structure ComplexSL2KAN where
  k : Matrix (Fin 2) (Fin 2) ℂ
  a : ℝ
  z : ℂ
  k_unitary : kᴴ * k = 1
  k_det : k.det = 1
  a_pos : 0 < a

instance : Inhabited ComplexSL2KAN where
  default := {
    k := 1
    a := 1
    z := 0
    k_unitary := by
      ext i j
      fin_cases i <;> fin_cases j <;> {
        simp only [mul_apply, Fin.sum_univ_two, conjTranspose_apply, one_apply]
        norm_num
      }
    k_det := by
      exact det_one
    a_pos := zero_lt_one
  }

def ComplexSL2KAN.A_mat (I : ComplexSL2KAN) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(I.a : ℂ), 0; 0, ((I.a : ℂ)⁻¹)]

def ComplexSL2KAN.N_mat (I : ComplexSL2KAN) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, I.z; 0, 1]

def ComplexSL2KAN.product (I : ComplexSL2KAN) : Matrix (Fin 2) (Fin 2) ℂ :=
  I.k * (I.A_mat * I.N_mat)

lemma complexSL2KAN_product_entries (I : ComplexSL2KAN) :
    I.product 0 0 = I.k 0 0 * (I.a : ℂ) ∧
    I.product 1 0 = I.k 1 0 * (I.a : ℂ) ∧
    I.product 0 1 = I.k 0 0 * ((I.a : ℂ) * I.z) + I.k 0 1 * (I.a : ℂ)⁻¹ ∧
    I.product 1 1 = I.k 1 0 * ((I.a : ℂ) * I.z) + I.k 1 1 * (I.a : ℂ)⁻¹ := by
  dsimp [ComplexSL2KAN.product, ComplexSL2KAN.A_mat, ComplexSL2KAN.N_mat]
  rw [mul_fin_two]
  simp only [mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp; ring
  · dsimp; ring
  · dsimp; ring
  · dsimp; ring

theorem complexSL2KAN_ext (I₁ I₂ : ComplexSL2KAN)
    (hk : I₁.k = I₂.k) (ha : I₁.a = I₂.a) (hz : I₁.z = I₂.z) : I₁ = I₂ := by
  cases I₁
  cases I₂
  dsimp at hk ha hz
  subst hk ha hz
  rfl

/-- Structure representing the Iwasawa K A N decomposition in GL(2, ℂ). -/
structure ComplexGL2KAN where
  k : Matrix (Fin 2) (Fin 2) ℂ
  a₁ : ℝ
  a₂ : ℝ
  z : ℂ
  k_unitary : kᴴ * k = 1
  a₁_pos : 0 < a₁
  a₂_pos : 0 < a₂

instance : Inhabited ComplexGL2KAN where
  default := {
    k := 1
    a₁ := 1
    a₂ := 1
    z := 0
    k_unitary := by
      ext i j
      fin_cases i <;> fin_cases j <;> {
        simp only [mul_apply, Fin.sum_univ_two, conjTranspose_apply, one_apply]
        norm_num
      }
    a₁_pos := zero_lt_one
    a₂_pos := zero_lt_one
  }

def ComplexGL2KAN.A_mat (I : ComplexGL2KAN) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(I.a₁ : ℂ), 0; 0, (I.a₂ : ℂ)]

def ComplexGL2KAN.N_mat (I : ComplexGL2KAN) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, I.z; 0, 1]

def ComplexGL2KAN.product (I : ComplexGL2KAN) : Matrix (Fin 2) (Fin 2) ℂ :=
  I.k * (I.A_mat * I.N_mat)

lemma complexGL2KAN_product_entries (I : ComplexGL2KAN) :
    I.product 0 0 = I.k 0 0 * (I.a₁ : ℂ) ∧
    I.product 1 0 = I.k 1 0 * (I.a₁ : ℂ) ∧
    I.product 0 1 = I.k 0 0 * ((I.a₁ : ℂ) * I.z) + I.k 0 1 * (I.a₂ : ℂ) ∧
    I.product 1 1 = I.k 1 0 * ((I.a₁ : ℂ) * I.z) + I.k 1 1 * (I.a₂ : ℂ) := by
  dsimp [ComplexGL2KAN.product, ComplexGL2KAN.A_mat, ComplexGL2KAN.N_mat]
  rw [mul_fin_two]
  simp only [mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp; ring
  · dsimp; ring
  · dsimp; ring
  · dsimp; ring

theorem complexGL2KAN_ext (I₁ I₂ : ComplexGL2KAN)
    (hk : I₁.k = I₂.k) (ha₁ : I₁.a₁ = I₂.a₁) (ha₂ : I₁.a₂ = I₂.a₂) (hz : I₁.z = I₂.z) : I₁ = I₂ := by
  cases I₁
  cases I₂
  dsimp at hk ha₁ ha₂ hz
  subst hk ha₁ ha₂ hz
  rfl

/-- SL(2, ℂ) Iwasawa K A N decomposition existence and uniqueness. -/
theorem sl2_complex_iwasawa_kan_exists_unique (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) :
    ∃! I : ComplexSL2KAN, I.product = M := by
  have hr2_pos : 0 < Complex.normSq (M 0 0) + Complex.normSq (M 1 0) := by
    by_contra hc
    have h_le : Complex.normSq (M 0 0) + Complex.normSq (M 1 0) ≤ 0 := not_lt.mp hc
    have h00_zero : Complex.normSq (M 0 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (M 0 0), Complex.normSq_nonneg (M 1 0)]
    have h10_zero : Complex.normSq (M 1 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (M 0 0), Complex.normSq_nonneg (M 1 0)]
    have hM00 : M 0 0 = 0 := Complex.normSq_eq_zero.mp h00_zero
    have hM10 : M 1 0 = 0 := Complex.normSq_eq_zero.mp h10_zero
    have hdet_zero : M.det = 0 := by
      rw [det_fin_two, hM00, hM10]
      ring
    rw [hdet_zero] at hM
    exact zero_ne_one hM
  let r := Real.sqrt (Complex.normSq (M 0 0) + Complex.normSq (M 1 0))
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hr2_pos
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  have hrC_ne_zero : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr_ne_zero
  have hr2_nonneg : 0 ≤ Complex.normSq (M 0 0) + Complex.normSq (M 1 0) := le_of_lt hr2_pos
  have hr_sq : r ^ 2 = Complex.normSq (M 0 0) + Complex.normSq (M 1 0) := Real.sq_sqrt hr2_nonneg
  have hrC_sq_val : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hrC_sq_sum : (r : ℂ) ^ 2 = conj (M 0 0) * M 0 0 + conj (M 1 0) * M 1 0 := by
    rw [hrC_sq_val, hr_sq]
    push_cast
    rw [← conj_mul_self_eq_normSq, ← conj_mul_self_eq_normSq]
  have hrC_sq_ne_zero : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hrC_ne_zero
  let k : Matrix (Fin 2) (Fin 2) ℂ :=
    !![M 0 0 / (r : ℂ), - conj (M 1 0) / (r : ℂ);
       M 1 0 / (r : ℂ), conj (M 0 0) / (r : ℂ)]
  have hk_unitary : kᴴ * k = 1 := by
    exact k_mat_unitary (M 0 0) (M 1 0) r hrC_sq_sum hrC_sq_ne_zero
  have hk_det : k.det = 1 := by
    exact k_mat_det (M 0 0) (M 1 0) r hrC_sq_sum hrC_sq_ne_zero
  let z : ℂ := (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) / (r : ℂ) ^ 2
  let I_can : ComplexSL2KAN := {
    k := k
    a := r
    z := z
    k_unitary := hk_unitary
    k_det := hk_det
    a_pos := hr_pos
  }
  have h_prod : I_can.product = M := by
    dsimp [ComplexSL2KAN.product, ComplexSL2KAN.A_mat, ComplexSL2KAN.N_mat, I_can, k, z]
    rw [mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp
      simp only [mul_zero, add_zero, mul_one]
      exact div_mul_cancel₀ (M 0 0) hrC_ne_zero
    · dsimp
      simp only [zero_mul, add_zero, zero_add, mul_one]
      have hr_mul_inv : (- conj (M 1 0) / (r : ℂ)) * (r : ℂ)⁻¹ = - (conj (M 1 0) / (r : ℂ) ^ 2) := by
        have : (- conj (M 1 0) / (r : ℂ)) * (r : ℂ)⁻¹ = - (conj (M 1 0) * ((r : ℂ)⁻¹ * (r : ℂ)⁻¹)) := by
          ring
        rw [this]
        have h_inv : (r : ℂ)⁻¹ * (r : ℂ)⁻¹ = ((r : ℂ) ^ 2)⁻¹ := by
          rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [← mul_assoc, div_mul_cancel₀ (M 0 0) hrC_ne_zero, hr_mul_inv]
      have h_alg : M 0 0 * ((conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) / (r : ℂ) ^ 2) +
          - (conj (M 1 0) / (r : ℂ) ^ 2) =
          (M 0 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) - conj (M 1 0)) / (r : ℂ) ^ 2 := by
        ring
      rw [h_alg]
      have hdet_sub : M 0 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) - conj (M 1 0) = (r : ℂ) ^ 2 * M 0 1 := by
        have hdet_val : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
        rw [hM] at hdet_val
        rw [hrC_sq_sum]
        linear_combination - conj (M 1 0) * hdet_val
      rw [hdet_sub]
      exact mul_div_cancel_left₀ (M 0 1) hrC_sq_ne_zero
    · dsimp
      simp only [mul_zero, add_zero, mul_one]
      exact div_mul_cancel₀ (M 1 0) hrC_ne_zero
    · dsimp
      simp only [zero_mul, add_zero, zero_add, mul_one]
      have hr_mul_inv : (conj (M 0 0) / (r : ℂ)) * (r : ℂ)⁻¹ = conj (M 0 0) / (r : ℂ) ^ 2 := by
        have : (conj (M 0 0) / (r : ℂ)) * (r : ℂ)⁻¹ = conj (M 0 0) * ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) := by
          ring
        rw [this]
        have h_inv : (r : ℂ)⁻¹ * (r : ℂ)⁻¹ = ((r : ℂ) ^ 2)⁻¹ := by
          rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [← mul_assoc, div_mul_cancel₀ (M 1 0) hrC_ne_zero, hr_mul_inv]
      have h_alg : M 1 0 * ((conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) / (r : ℂ) ^ 2) +
          (conj (M 0 0) / (r : ℂ) ^ 2) =
          (M 1 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) + conj (M 0 0)) / (r : ℂ) ^ 2 := by
        ring
      rw [h_alg]
      have hdet_sub : M 1 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) + conj (M 0 0) = (r : ℂ) ^ 2 * M 1 1 := by
        have hdet_val : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
        rw [hM] at hdet_val
        rw [hrC_sq_sum]
        linear_combination conj (M 0 0) * hdet_val
      rw [hdet_sub]
      exact mul_div_cancel_left₀ (M 1 1) hrC_sq_ne_zero
  refine ⟨I_can, h_prod, ?_⟩
  intro J hJ
  have hJ_entries := complexSL2KAN_product_entries J
  have hI_entries := complexSL2KAN_product_entries I_can
  have hM00 : M 0 0 = J.k 0 0 * (J.a : ℂ) := by rw [← hJ, hJ_entries.1]
  have hM10 : M 1 0 = J.k 1 0 * (J.a : ℂ) := by rw [← hJ, hJ_entries.2.1]
  have hM01 : M 0 1 = J.k 0 0 * ((J.a : ℂ) * J.z) + J.k 0 1 * (J.a : ℂ)⁻¹ := by rw [← hJ, hJ_entries.2.2.1]
  have hM11 : M 1 1 = J.k 1 0 * ((J.a : ℂ) * J.z) + J.k 1 1 * (J.a : ℂ)⁻¹ := by rw [← hJ, hJ_entries.2.2.2]
  have hJ_orth := unitary_fin_two_entries J.k J.k_unitary
  have hJ_orth00 := hJ_orth.1
  have hJ_orth01 := hJ_orth.2
  have hM00_conj : conj (M 0 0) = conj (J.k 0 0) * (J.a : ℂ) := by
    rw [hM00, map_mul, Complex.conj_ofReal]
  have hM10_conj : conj (M 1 0) = conj (J.k 1 0) * (J.a : ℂ) := by
    rw [hM10, map_mul, Complex.conj_ofReal]
  have hrC_eq_Ja : (r : ℂ) ^ 2 = (J.a : ℂ) ^ 2 := by
    rw [hrC_sq_sum, hM00_conj, hM10_conj, hM00, hM10]
    linear_combination (J.a : ℂ) ^ 2 * hJ_orth00
  have hr_sq_eq : r ^ 2 = J.a ^ 2 := by
    exact_mod_cast hrC_eq_Ja
  have ha_eq : J.a = r := sq_eq_sq_pos J.a_pos hr_pos hr_sq_eq.symm
  have hz_eq : J.z = z := by
    have h_alg : conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1 = (r : ℂ) ^ 2 * J.z := by
      rw [hM00_conj, hM10_conj, hM01, hM11]
      linear_combination ((J.a : ℂ) ^ 2 * J.z) * hJ_orth00 + ((J.a : ℂ) * (J.a : ℂ)⁻¹) * hJ_orth01 + J.z * hrC_eq_Ja.symm
    dsimp [z]
    rw [h_alg]
    exact (mul_div_cancel_left₀ J.z hrC_sq_ne_zero).symm
  have hk00 : J.k 0 0 = k 0 0 := by
    have h1 : J.k 0 0 * (r : ℂ) = M 0 0 := by
      have : (J.a : ℂ) = (r : ℂ) := by exact_mod_cast ha_eq
      rw [← this, ← hM00]
    have h2 : k 0 0 * (r : ℂ) = M 0 0 := by
      have h := hI_entries.1
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 0 0 - k 0 0) * (r : ℂ) = 0 := by
      calc (J.k 0 0 - k 0 0) * (r : ℂ) = J.k 0 0 * (r : ℂ) - k 0 0 * (r : ℂ) := by ring
      _ = M 0 0 - M 0 0 := by rw [h1, h2]
      _ = 0 := sub_self (M 0 0)
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr hr => exact False.elim (hrC_ne_zero hr)
  have hk10 : J.k 1 0 = k 1 0 := by
    have h1 : J.k 1 0 * (r : ℂ) = M 1 0 := by
      have : (J.a : ℂ) = (r : ℂ) := by exact_mod_cast ha_eq
      rw [← this, ← hM10]
    have h2 : k 1 0 * (r : ℂ) = M 1 0 := by
      have h := hI_entries.2.1
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 1 0 - k 1 0) * (r : ℂ) = 0 := by
      calc (J.k 1 0 - k 1 0) * (r : ℂ) = J.k 1 0 * (r : ℂ) - k 1 0 * (r : ℂ) := by ring
      _ = M 1 0 - M 1 0 := by rw [h1, h2]
      _ = 0 := sub_self (M 1 0)
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr hr => exact False.elim (hrC_ne_zero hr)
  have hrC_inv_ne_zero : (r : ℂ)⁻¹ ≠ 0 := inv_ne_zero hrC_ne_zero
  have hk01 : J.k 0 1 = k 0 1 := by
    have h1 : J.k 0 0 * ((r : ℂ) * z) + J.k 0 1 * (r : ℂ)⁻¹ = M 0 1 := by
      have haC : (J.a : ℂ) = (r : ℂ) := by exact_mod_cast ha_eq
      rw [← haC, ← hz_eq, ← hM01]
    have h2 : k 0 0 * ((r : ℂ) * z) + k 0 1 * (r : ℂ)⁻¹ = M 0 1 := by
      have h := hI_entries.2.2.1
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 0 1 - k 0 1) * (r : ℂ)⁻¹ = 0 := by
      linear_combination h1 - h2 - (r : ℂ) * z * hk00
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr hinv => exact False.elim (hrC_inv_ne_zero hinv)
  have hk11 : J.k 1 1 = k 1 1 := by
    have h1 : J.k 1 0 * ((r : ℂ) * z) + J.k 1 1 * (r : ℂ)⁻¹ = M 1 1 := by
      have haC : (J.a : ℂ) = (r : ℂ) := by exact_mod_cast ha_eq
      rw [← haC, ← hz_eq, ← hM11]
    have h2 : k 1 0 * ((r : ℂ) * z) + k 1 1 * (r : ℂ)⁻¹ = M 1 1 := by
      have h := hI_entries.2.2.2
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 1 1 - k 1 1) * (r : ℂ)⁻¹ = 0 := by
      linear_combination h1 - h2 - (r : ℂ) * z * hk10
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr hinv => exact False.elim (hrC_inv_ne_zero hinv)
  have hk : J.k = k := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hk00
    · exact hk01
    · exact hk10
    · exact hk11
  exact complexSL2KAN_ext J I_can hk ha_eq hz_eq

/-- GL(2, ℂ) Iwasawa K A N decomposition existence and uniqueness. -/
theorem gl2_complex_iwasawa_kan_exists_unique (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) :
    ∃! I : ComplexGL2KAN, I.product = M := by
  have hr2_pos : 0 < Complex.normSq (M 0 0) + Complex.normSq (M 1 0) := by
    by_contra hc
    have h_le : Complex.normSq (M 0 0) + Complex.normSq (M 1 0) ≤ 0 := not_lt.mp hc
    have h00_zero : Complex.normSq (M 0 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (M 0 0), Complex.normSq_nonneg (M 1 0)]
    have h10_zero : Complex.normSq (M 1 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (M 0 0), Complex.normSq_nonneg (M 1 0)]
    have hM00 : M 0 0 = 0 := Complex.normSq_eq_zero.mp h00_zero
    have hM10 : M 1 0 = 0 := Complex.normSq_eq_zero.mp h10_zero
    have hdet_zero : M.det = 0 := by
      rw [det_fin_two, hM00, hM10]
      ring
    exact hM hdet_zero
  let r : ℝ := Real.sqrt (Complex.normSq (M 0 0) + Complex.normSq (M 1 0))
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hr2_pos
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  have hrC_ne_zero : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr_ne_zero
  have hr2_nonneg : 0 ≤ Complex.normSq (M 0 0) + Complex.normSq (M 1 0) := le_of_lt hr2_pos
  have hr_sq : r ^ 2 = Complex.normSq (M 0 0) + Complex.normSq (M 1 0) := Real.sq_sqrt hr2_nonneg
  have hrC_sq_val : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hrC_sq_sum : (r : ℂ) ^ 2 = conj (M 0 0) * M 0 0 + conj (M 1 0) * M 1 0 := by
    rw [hrC_sq_val, hr_sq]
    push_cast
    rw [← conj_mul_self_eq_normSq, ← conj_mul_self_eq_normSq]
  have hrC_sq_ne_zero : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hrC_ne_zero
  have hnormSq_det_pos : 0 < Complex.normSq M.det := Complex.normSq_pos.mpr hM
  let δ : ℝ := Real.sqrt (Complex.normSq M.det)
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr hnormSq_det_pos
  have hδ_ne_zero : δ ≠ 0 := ne_of_gt hδ_pos
  have hδC_ne_zero : (δ : ℂ) ≠ 0 := by
    exact_mod_cast hδ_ne_zero
  have hδ_sq : δ ^ 2 = Complex.normSq M.det := Real.sq_sqrt (le_of_lt hnormSq_det_pos)
  let a₁ : ℝ := r
  let a₂ : ℝ := δ / r
  have ha₁_pos : 0 < a₁ := hr_pos
  have ha₂_pos : 0 < a₂ := div_pos hδ_pos hr_pos
  have ha₂C_ne_zero : (a₂ : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt ha₂_pos
  let ω : ℂ := M.det / (δ : ℂ)
  have hω_norm : conj ω * ω = 1 := by
    dsimp [ω]
    rw [map_div₀, Complex.conj_ofReal]
    have h_div : (conj M.det / (δ : ℂ)) * (M.det / (δ : ℂ)) = (conj M.det * M.det) / ((δ : ℂ) ^ 2) := by
      ring
    rw [h_div, conj_mul_self_eq_normSq]
    have : ((δ : ℂ) ^ 2) = ((δ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [this, hδ_sq]
    have h_ne : ((Complex.normSq M.det : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hnormSq_det_pos
    exact div_self h_ne
  let k : Matrix (Fin 2) (Fin 2) ℂ :=
    !![M 0 0 / (r : ℂ), - ω * conj (M 1 0) / (r : ℂ);
       M 1 0 / (r : ℂ), ω * conj (M 0 0) / (r : ℂ)]
  have hk_unitary : kᴴ * k = 1 := by
    exact k_gl2_unitary (M 0 0) (M 1 0) ω r hω_norm hrC_sq_sum hrC_sq_ne_zero
  let z : ℂ := (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) / (r : ℂ) ^ 2
  let I_can : ComplexGL2KAN := {
    k := k
    a₁ := a₁
    a₂ := a₂
    z := z
    k_unitary := hk_unitary
    a₁_pos := ha₁_pos
    a₂_pos := ha₂_pos
  }
  have h_prod : I_can.product = M := by
    dsimp [ComplexGL2KAN.product, ComplexGL2KAN.A_mat, ComplexGL2KAN.N_mat, I_can, k, z, a₁, a₂]
    rw [mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp
      simp only [mul_zero, add_zero, mul_one]
      exact div_mul_cancel₀ (M 0 0) hrC_ne_zero
    · dsimp
      simp only [zero_mul, add_zero, zero_add, mul_one]
      have h_ωδ : ω * ((δ / r : ℝ) : ℂ) = M.det / (r : ℂ) := by
        dsimp [ω]
        have : ((δ / r : ℝ) : ℂ) = (δ : ℂ) / (r : ℂ) := by
          push_cast
          rfl
        rw [this]
        have h_alg : (M.det / (δ : ℂ)) * ((δ : ℂ) / (r : ℂ)) = (M.det * (δ : ℂ)) / ((r : ℂ) * (δ : ℂ)) := by
          ring
        rw [h_alg]
        exact mul_div_mul_right M.det (r : ℂ) hδC_ne_zero
      have hr_mul_inv : (- ω * conj (M 1 0) / (r : ℂ)) * ((δ / r : ℝ) : ℂ) = - (conj (M 1 0) * M.det / (r : ℂ) ^ 2) := by
        have : (- ω * conj (M 1 0) / (r : ℂ)) * ((δ / r : ℝ) : ℂ) = - conj (M 1 0) * (ω * ((δ / r : ℝ) : ℂ)) / (r : ℂ) := by
          ring
        rw [this, h_ωδ]
        have h_alg : - conj (M 1 0) * (M.det / (r : ℂ)) / (r : ℂ) = - (conj (M 1 0) * M.det) * ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) := by
          ring
        rw [h_alg]
        have h_inv : (r : ℂ)⁻¹ * (r : ℂ)⁻¹ = ((r : ℂ) ^ 2)⁻¹ := by
          rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
        ring
      rw [← mul_assoc, div_mul_cancel₀ (M 0 0) hrC_ne_zero, hr_mul_inv]
      have h_alg : M 0 0 * ((conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) / (r : ℂ) ^ 2) +
          - (conj (M 1 0) * M.det / (r : ℂ) ^ 2) =
          (M 0 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) - conj (M 1 0) * M.det) / (r : ℂ) ^ 2 := by
        ring
      rw [h_alg]
      have hdet_sub : M 0 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) - conj (M 1 0) * M.det = (r : ℂ) ^ 2 * M 0 1 := by
        have hdet_val : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
        rw [hrC_sq_sum]
        linear_combination - conj (M 1 0) * hdet_val
      rw [hdet_sub]
      exact mul_div_cancel_left₀ (M 0 1) hrC_sq_ne_zero
    · dsimp
      simp only [mul_zero, add_zero, mul_one]
      exact div_mul_cancel₀ (M 1 0) hrC_ne_zero
    · dsimp
      simp only [zero_mul, add_zero, zero_add, mul_one]
      have h_ωδ : ω * ((δ / r : ℝ) : ℂ) = M.det / (r : ℂ) := by
        dsimp [ω]
        have : ((δ / r : ℝ) : ℂ) = (δ : ℂ) / (r : ℂ) := by
          push_cast
          rfl
        rw [this]
        have h_alg : (M.det / (δ : ℂ)) * ((δ : ℂ) / (r : ℂ)) = (M.det * (δ : ℂ)) / ((r : ℂ) * (δ : ℂ)) := by
          ring
        rw [h_alg]
        exact mul_div_mul_right M.det (r : ℂ) hδC_ne_zero
      have hr_mul_inv : (ω * conj (M 0 0) / (r : ℂ)) * ((δ / r : ℝ) : ℂ) = conj (M 0 0) * M.det / (r : ℂ) ^ 2 := by
        have : (ω * conj (M 0 0) / (r : ℂ)) * ((δ / r : ℝ) : ℂ) = conj (M 0 0) * (ω * ((δ / r : ℝ) : ℂ)) / (r : ℂ) := by
          ring
        rw [this, h_ωδ]
        have h_alg : conj (M 0 0) * (M.det / (r : ℂ)) / (r : ℂ) = (conj (M 0 0) * M.det) * ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) := by
          ring
        rw [h_alg]
        have h_inv : (r : ℂ)⁻¹ * (r : ℂ)⁻¹ = ((r : ℂ) ^ 2)⁻¹ := by
          rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [← mul_assoc, div_mul_cancel₀ (M 1 0) hrC_ne_zero, hr_mul_inv]
      have h_alg : M 1 0 * ((conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) / (r : ℂ) ^ 2) +
          (conj (M 0 0) * M.det / (r : ℂ) ^ 2) =
          (M 1 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) + conj (M 0 0) * M.det) / (r : ℂ) ^ 2 := by
        ring
      rw [h_alg]
      have hdet_sub : M 1 0 * (conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1) + conj (M 0 0) * M.det = (r : ℂ) ^ 2 * M 1 1 := by
        have hdet_val : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
        rw [hrC_sq_sum]
        linear_combination conj (M 0 0) * hdet_val
      rw [hdet_sub]
      exact mul_div_cancel_left₀ (M 1 1) hrC_sq_ne_zero
  refine ⟨I_can, h_prod, ?_⟩
  intro J hJ
  have hJ_entries := complexGL2KAN_product_entries J
  have hI_entries := complexGL2KAN_product_entries I_can
  have hM00 : M 0 0 = J.k 0 0 * (J.a₁ : ℂ) := by rw [← hJ, hJ_entries.1]
  have hM10 : M 1 0 = J.k 1 0 * (J.a₁ : ℂ) := by rw [← hJ, hJ_entries.2.1]
  have hM01 : M 0 1 = J.k 0 0 * ((J.a₁ : ℂ) * J.z) + J.k 0 1 * (J.a₂ : ℂ) := by rw [← hJ, hJ_entries.2.2.1]
  have hM11 : M 1 1 = J.k 1 0 * ((J.a₁ : ℂ) * J.z) + J.k 1 1 * (J.a₂ : ℂ) := by rw [← hJ, hJ_entries.2.2.2]
  have hJ_orth := unitary_fin_two_entries J.k J.k_unitary
  have hJ_orth00 := hJ_orth.1
  have hJ_orth01 := hJ_orth.2
  have hM00_conj : conj (M 0 0) = conj (J.k 0 0) * (J.a₁ : ℂ) := by
    rw [hM00, map_mul, Complex.conj_ofReal]
  have hM10_conj : conj (M 1 0) = conj (J.k 1 0) * (J.a₁ : ℂ) := by
    rw [hM10, map_mul, Complex.conj_ofReal]
  have hrC_eq_Ja₁ : (r : ℂ) ^ 2 = (J.a₁ : ℂ) ^ 2 := by
    rw [hrC_sq_sum, hM00_conj, hM10_conj, hM00, hM10]
    linear_combination (J.a₁ : ℂ) ^ 2 * hJ_orth00
  have hr_sq_eq : r ^ 2 = J.a₁ ^ 2 := by
    exact_mod_cast hrC_eq_Ja₁
  have ha₁_eq : J.a₁ = a₁ := sq_eq_sq_pos J.a₁_pos hr_pos hr_sq_eq.symm
  have hdet_A : J.A_mat.det = (J.a₁ : ℂ) * (J.a₂ : ℂ) := det_diag_two (J.a₁ : ℂ) (J.a₂ : ℂ)
  have hdet_N : J.N_mat.det = 1 := det_upper_tri_one J.z
  have hdet_M : M.det = J.k.det * ((J.a₁ : ℂ) * (J.a₂ : ℂ)) := by
    have h : M.det = J.product.det := by rw [hJ]
    dsimp [ComplexGL2KAN.product] at h
    rw [det_mul, det_mul, hdet_A, hdet_N, mul_one] at h
    exact h
  have h_normSq_M : Complex.normSq M.det = (J.a₁ * J.a₂) ^ 2 := by
    rw [hdet_M, Complex.normSq_mul]
    have hk_det_one : Complex.normSq J.k.det = 1 := unitary_det_normSq_one J.k J.k_unitary
    rw [hk_det_one, one_mul]
    have : ((J.a₁ : ℂ) * (J.a₂ : ℂ)) = ((J.a₁ * J.a₂ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.normSq_ofReal, sq]
  have ha2_sq : (J.a₁ * J.a₂) ^ 2 = δ ^ 2 := by
    rw [← h_normSq_M, hδ_sq]
  have ha12_eq : J.a₁ * J.a₂ = δ :=
    sq_eq_sq_pos (mul_pos J.a₁_pos J.a₂_pos) hδ_pos ha2_sq
  have ha₂_eq : J.a₂ = a₂ := by
    dsimp [a₂]
    have h1 : J.a₂ * r = δ := by
      have h2 : r * J.a₂ = δ := by
        have h3 : (r : ℝ) = a₁ := rfl
        rw [h3, ← ha₁_eq, ha12_eq]
      rw [mul_comm]
      exact h2
    exact (eq_div_iff hr_ne_zero).mpr h1
  have hz_eq : J.z = z := by
    have h_alg : conj (M 0 0) * M 0 1 + conj (M 1 0) * M 1 1 = (r : ℂ) ^ 2 * J.z := by
      rw [hM00_conj, hM10_conj, hM01, hM11]
      linear_combination ((J.a₁ : ℂ) ^ 2 * J.z) * hJ_orth00 + ((J.a₁ : ℂ) * (J.a₂ : ℂ)) * hJ_orth01 + J.z * hrC_eq_Ja₁.symm
    dsimp [z]
    rw [h_alg]
    exact (mul_div_cancel_left₀ J.z hrC_sq_ne_zero).symm
  have hk00 : J.k 0 0 = k 0 0 := by
    have h1 : J.k 0 0 * (r : ℂ) = M 0 0 := by
      have : (J.a₁ : ℂ) = (r : ℂ) := by exact_mod_cast ha₁_eq
      rw [← this, ← hM00]
    have h2 : k 0 0 * (r : ℂ) = M 0 0 := by
      have h := hI_entries.1
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 0 0 - k 0 0) * (r : ℂ) = 0 := by
      calc (J.k 0 0 - k 0 0) * (r : ℂ) = J.k 0 0 * (r : ℂ) - k 0 0 * (r : ℂ) := by ring
      _ = M 0 0 - M 0 0 := by rw [h1, h2]
      _ = 0 := sub_self (M 0 0)
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr hr => exact False.elim (hrC_ne_zero hr)
  have hk10 : J.k 1 0 = k 1 0 := by
    have h1 : J.k 1 0 * (r : ℂ) = M 1 0 := by
      have : (J.a₁ : ℂ) = (r : ℂ) := by exact_mod_cast ha₁_eq
      rw [← this, ← hM10]
    have h2 : k 1 0 * (r : ℂ) = M 1 0 := by
      have h := hI_entries.2.1
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 1 0 - k 1 0) * (r : ℂ) = 0 := by
      calc (J.k 1 0 - k 1 0) * (r : ℂ) = J.k 1 0 * (r : ℂ) - k 1 0 * (r : ℂ) := by ring
      _ = M 1 0 - M 1 0 := by rw [h1, h2]
      _ = 0 := sub_self (M 1 0)
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr hr => exact False.elim (hrC_ne_zero hr)
  have ha₂C_ne_zero' : (a₂ : ℂ) ≠ 0 := ha₂C_ne_zero
  have hk01 : J.k 0 1 = k 0 1 := by
    have h1 : J.k 0 0 * ((r : ℂ) * z) + J.k 0 1 * (a₂ : ℂ) = M 0 1 := by
      have ha₁C : (J.a₁ : ℂ) = (r : ℂ) := by exact_mod_cast ha₁_eq
      have ha₂C : (J.a₂ : ℂ) = (a₂ : ℂ) := by exact_mod_cast ha₂_eq
      rw [← ha₁C, ← ha₂C, ← hz_eq, ← hM01]
    have h2 : k 0 0 * ((r : ℂ) * z) + k 0 1 * (a₂ : ℂ) = M 0 1 := by
      have h := hI_entries.2.2.1
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 0 1 - k 0 1) * (a₂ : ℂ) = 0 := by
      linear_combination h1 - h2 - (r : ℂ) * z * hk00
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr ha₂ => exact False.elim (ha₂C_ne_zero' ha₂)
  have hk11 : J.k 1 1 = k 1 1 := by
    have h1 : J.k 1 0 * ((r : ℂ) * z) + J.k 1 1 * (a₂ : ℂ) = M 1 1 := by
      have ha₁C : (J.a₁ : ℂ) = (r : ℂ) := by exact_mod_cast ha₁_eq
      have ha₂C : (J.a₂ : ℂ) = (a₂ : ℂ) := by exact_mod_cast ha₂_eq
      rw [← ha₁C, ← ha₂C, ← hz_eq, ← hM11]
    have h2 : k 1 0 * ((r : ℂ) * z) + k 1 1 * (a₂ : ℂ) = M 1 1 := by
      have h := hI_entries.2.2.2
      rw [h_prod] at h
      exact h.symm
    have h3 : (J.k 1 1 - k 1 1) * (a₂ : ℂ) = 0 := by
      linear_combination h1 - h2 - (r : ℂ) * z * hk10
    cases mul_eq_zero.mp h3 with
    | inl hsub => exact sub_eq_zero.mp hsub
    | inr ha₂ => exact False.elim (ha₂C_ne_zero' ha₂)
  have hk : J.k = k := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hk00
    · exact hk01
    · exact hk10
    · exact hk11
  exact complexGL2KAN_ext J I_can hk ha₁_eq ha₂_eq hz_eq

/-- OpenGauss T16 non-commutativity witness in Matrix (Fin 2) (Fin 2) ℂ. -/
theorem matrix_carrier_Complex_noncommutative :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℂ, M * N ≠ N * M := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  let N : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
  use M, N
  intro h
  have h00 : (M * N) 0 0 = (N * M) 0 0 := by rw [h]
  rw [mul_fin_two, mul_fin_two] at h00
  dsimp [M, N] at h00
  have h_one_zero : (1 : ℂ) = 0 := by
    linear_combination h00
  exact one_ne_zero h_one_zero

/-- 2x2 complex Cayley-Hamilton identity. -/
lemma matrix_fin_two_cayley_hamilton (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A - (A 0 0 + A 1 1) • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [mul_apply, Fin.sum_univ_two, det_fin_two]
    ring
  }

/-- Uniqueness of the GL(2, ℂ) polar decomposition factor P via Cayley-Hamilton. -/
lemma gl2_complex_polar_P_unique_of_cayley_hamilton
    (P₁ P₂ : Matrix (Fin 2) (Fin 2) ℂ) (S : Matrix (Fin 2) (Fin 2) ℂ) (δ τ : ℂ) (hτ : τ ≠ 0)
    (hPP₁ : P₁ * P₁ = S) (hPP₂ : P₂ * P₂ = S)
    (hdet₁ : P₁.det = δ) (hdet₂ : P₂.det = δ)
    (htr₁ : P₁ 0 0 + P₁ 1 1 = τ) (htr₂ : P₂ 0 0 + P₂ 1 1 = τ) :
    P₁ = P₂ := by
  have hCH₁ := matrix_fin_two_cayley_hamilton P₁
  have hCH₂ := matrix_fin_two_cayley_hamilton P₂
  rw [hPP₁, hdet₁, htr₁] at hCH₁
  rw [hPP₂, hdet₂, htr₂] at hCH₂
  ext i j
  have h1 : (S - τ • P₁ + δ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j = 0 := by
    rw [hCH₁, Matrix.zero_apply]
  have h2 : (S - τ • P₂ + δ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j = 0 := by
    rw [hCH₂, Matrix.zero_apply]
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
  have h_diff : τ * (P₁ i j - P₂ i j) = 0 := by
    linear_combination -h1 + h2
  cases mul_eq_zero.mp h_diff with
  | inl htau => exact False.elim (hτ htau)
  | inr hsub => exact sub_eq_zero.mp hsub

/-- Constructive GL(2, ℂ) unitary polar decomposition. -/
theorem gl2_complex_polar_decomposition_closed_form
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) :
    ∃ (U P : Matrix (Fin 2) (Fin 2) ℂ),
      M = U * P ∧
      Uᴴ * U = 1 ∧
      U * Uᴴ = 1 ∧
      Pᴴ = P ∧
      P * P = Mᴴ * M ∧
      P.det = (Real.sqrt (Complex.normSq M.det) : ℂ) ∧
      ∀ v : Fin 2 → ℂ, v ≠ 0 → 0 < ((star v ⬝ᵥ P.mulVec v).re) := by
  let S : Matrix (Fin 2) (Fin 2) ℂ := Mᴴ * M
  have hS_symm : Sᴴ = S := by
    dsimp [S]
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hS_01_conj : conj (S 0 1) = S 1 0 := by
    have : Sᴴ 1 0 = S 1 0 := by rw [hS_symm]
    dsimp [conjTranspose] at this
    exact this
  have hS_10_conj : conj (S 1 0) = S 0 1 := by
    rw [← hS_01_conj, Complex.conj_conj]
  have hS00_eq : S 0 0 = ((Complex.normSq (M 0 0) + Complex.normSq (M 1 0) : ℝ) : ℂ) := by
    simp only [S, mul_apply, Fin.sum_univ_two, conjTranspose_apply, star_eq_conj]
    rw [conj_mul_self_eq_normSq, conj_mul_self_eq_normSq]
    push_cast
    rfl
  have hS11_eq : S 1 1 = ((Complex.normSq (M 0 1) + Complex.normSq (M 1 1) : ℝ) : ℂ) := by
    simp only [S, mul_apply, Fin.sum_univ_two, conjTranspose_apply, star_eq_conj]
    rw [conj_mul_self_eq_normSq, conj_mul_self_eq_normSq]
    push_cast
    rfl
  have hS00_conj : conj (S 0 0) = S 0 0 := by
    rw [hS00_eq, Complex.conj_ofReal]
  have hS11_conj : conj (S 1 1) = S 1 1 := by
    rw [hS11_eq, Complex.conj_ofReal]
  let T : ℝ := Complex.normSq (M 0 0) + Complex.normSq (M 1 0) + Complex.normSq (M 0 1) + Complex.normSq (M 1 1)
  have h_trS : S 0 0 + S 1 1 = (T : ℂ) := by
    dsimp [T]
    rw [hS00_eq, hS11_eq]
    push_cast
    ring
  let δ : ℝ := Real.sqrt (Complex.normSq M.det)
  have hnormSq_det_pos : 0 < Complex.normSq M.det := Complex.normSq_pos.mpr hM
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr hnormSq_det_pos
  have hδ_sq : δ ^ 2 = Complex.normSq M.det := Real.sq_sqrt (le_of_lt hnormSq_det_pos)
  have h_detS : S.det = (δ : ℂ) ^ 2 := by
    dsimp [S]
    rw [det_mul, det_conjTranspose, star_eq_conj, conj_mul_self_eq_normSq, ← hδ_sq]
    push_cast
    rfl
  have hT_nonneg : 0 ≤ T := by
    have h1 := Complex.normSq_nonneg (M 0 0)
    have h2 := Complex.normSq_nonneg (M 1 0)
    have h3 := Complex.normSq_nonneg (M 0 1)
    have h4 := Complex.normSq_nonneg (M 1 1)
    positivity
  have h_sum_pos : 0 < T + 2 * δ := by
    positivity
  let τ : ℝ := Real.sqrt (T + 2 * δ)
  have hτ_pos : 0 < τ := Real.sqrt_pos.mpr h_sum_pos
  have hτ_ne_zero : τ ≠ 0 := ne_of_gt hτ_pos
  have hτC_ne_zero : (τ : ℂ) ≠ 0 := by
    exact_mod_cast hτ_ne_zero
  have hτ_sq : τ ^ 2 = T + 2 * δ := Real.sq_sqrt (le_of_lt h_sum_pos)
  have hτC_sq : (τ : ℂ) ^ 2 = (T : ℂ) + 2 * (δ : ℂ) := by
    have : ((τ ^ 2 : ℝ) : ℂ) = ((T + 2 * δ : ℝ) : ℂ) := by rw [hτ_sq]
    push_cast at this ⊢
    exact this
  have hτC_sq_ne_zero : (τ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hτC_ne_zero
  let P : Matrix (Fin 2) (Fin 2) ℂ :=
    !![(τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ)), (τ : ℂ)⁻¹ * S 0 1;
       (τ : ℂ)⁻¹ * S 1 0, (τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))]
  have hP_symm : Pᴴ = P := by
    change (!![(τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ)), (τ : ℂ)⁻¹ * S 0 1;
              (τ : ℂ)⁻¹ * S 1 0, (τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))]ᴴ : Matrix (Fin 2) (Fin 2) ℂ) =
            !![(τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ)), (τ : ℂ)⁻¹ * S 0 1;
              (τ : ℂ)⁻¹ * S 1 0, (τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))]
    rw [conjTranspose_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp
      rw [map_mul, Complex.conj_inv, Complex.conj_ofReal, map_add, hS00_conj, Complex.conj_ofReal]
    · dsimp
      rw [map_mul, Complex.conj_inv, Complex.conj_ofReal, hS_10_conj]
    · dsimp
      rw [map_mul, Complex.conj_inv, Complex.conj_ofReal, hS_01_conj]
    · dsimp
      rw [map_mul, Complex.conj_inv, Complex.conj_ofReal, map_add, hS11_conj, Complex.conj_ofReal]
  have hPP : P * P = Mᴴ * M := by
    change P * P = S
    rw [mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp
      have h_alg : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) +
          ((τ : ℂ)⁻¹ * S 0 1) * ((τ : ℂ)⁻¹ * S 1 0) =
          ((S 0 0 + (δ : ℂ)) ^ 2 + S 0 1 * S 1 0) / (τ : ℂ) ^ 2 := by
        have : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) +
            ((τ : ℂ)⁻¹ * S 0 1) * ((τ : ℂ)⁻¹ * S 1 0) =
            ((S 0 0 + (δ : ℂ)) ^ 2 + S 0 1 * S 1 0) * ((τ : ℂ)⁻¹ * (τ : ℂ)⁻¹) := by ring
        rw [this]
        have h_inv : (τ : ℂ)⁻¹ * (τ : ℂ)⁻¹ = ((τ : ℂ) ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [h_alg]
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := det_fin_two S
      have h_num : (S 0 0 + (δ : ℂ)) ^ 2 + S 0 1 * S 1 0 = S 0 0 * ((T : ℂ) + 2 * (δ : ℂ)) := by
        rw [← h_trS]
        linear_combination -h_detS + h_detS_val
      rw [h_num, ← hτC_sq]
      exact mul_div_cancel_right₀ (S 0 0) hτC_sq_ne_zero
    · dsimp
      have h_alg : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * S 0 1) +
          ((τ : ℂ)⁻¹ * S 0 1) * ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) =
          (S 0 1 * ((T : ℂ) + 2 * (δ : ℂ))) / (τ : ℂ) ^ 2 := by
        have : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * S 0 1) +
            ((τ : ℂ)⁻¹ * S 0 1) * ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) =
            (S 0 1 * (S 0 0 + S 1 1 + 2 * (δ : ℂ))) * ((τ : ℂ)⁻¹ * (τ : ℂ)⁻¹) := by ring
        rw [this, h_trS]
        have h_inv : (τ : ℂ)⁻¹ * (τ : ℂ)⁻¹ = ((τ : ℂ) ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [h_alg, ← hτC_sq]
      exact mul_div_cancel_right₀ (S 0 1) hτC_sq_ne_zero
    · dsimp
      have h_alg : ((τ : ℂ)⁻¹ * S 1 0) * ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) +
          ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * S 1 0) =
          (S 1 0 * ((T : ℂ) + 2 * (δ : ℂ))) / (τ : ℂ) ^ 2 := by
        have : ((τ : ℂ)⁻¹ * S 1 0) * ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) +
            ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * S 1 0) =
            (S 1 0 * (S 0 0 + S 1 1 + 2 * (δ : ℂ))) * ((τ : ℂ)⁻¹ * (τ : ℂ)⁻¹) := by ring
        rw [this, h_trS]
        have h_inv : (τ : ℂ)⁻¹ * (τ : ℂ)⁻¹ = ((τ : ℂ) ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [h_alg, ← hτC_sq]
      exact mul_div_cancel_right₀ (S 1 0) hτC_sq_ne_zero
    · dsimp
      have h_alg : ((τ : ℂ)⁻¹ * S 1 0) * ((τ : ℂ)⁻¹ * S 0 1) +
          ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) =
          ((S 1 1 + (δ : ℂ)) ^ 2 + S 0 1 * S 1 0) / (τ : ℂ) ^ 2 := by
        have : ((τ : ℂ)⁻¹ * S 1 0) * ((τ : ℂ)⁻¹ * S 0 1) +
            ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) =
            ((S 1 1 + (δ : ℂ)) ^ 2 + S 0 1 * S 1 0) * ((τ : ℂ)⁻¹ * (τ : ℂ)⁻¹) := by ring
        rw [this]
        have h_inv : (τ : ℂ)⁻¹ * (τ : ℂ)⁻¹ = ((τ : ℂ) ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [h_alg]
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := det_fin_two S
      have h_num : (S 1 1 + (δ : ℂ)) ^ 2 + S 0 1 * S 1 0 = S 1 1 * ((T : ℂ) + 2 * (δ : ℂ)) := by
        rw [← h_trS]
        linear_combination -h_detS + h_detS_val
      rw [h_num, ← hτC_sq]
      exact mul_div_cancel_right₀ (S 1 1) hτC_sq_ne_zero
  have hP_det : P.det = (Real.sqrt (Complex.normSq M.det) : ℂ) := by
    change P.det = (δ : ℂ)
    rw [det_fin_two]
    dsimp [P]
    have h_alg : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) -
        ((τ : ℂ)⁻¹ * S 0 1) * ((τ : ℂ)⁻¹ * S 1 0) =
        ((S 0 0 + (δ : ℂ)) * (S 1 1 + (δ : ℂ)) - S 0 1 * S 1 0) / (τ : ℂ) ^ 2 := by
      have : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) -
          ((τ : ℂ)⁻¹ * S 0 1) * ((τ : ℂ)⁻¹ * S 1 0) =
          ((S 0 0 + (δ : ℂ)) * (S 1 1 + (δ : ℂ)) - S 0 1 * S 1 0) * ((τ : ℂ)⁻¹ * (τ : ℂ)⁻¹) := by ring
      rw [this]
      have h_inv : (τ : ℂ)⁻¹ * (τ : ℂ)⁻¹ = ((τ : ℂ) ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
      rw [h_inv, div_eq_mul_inv]
    rw [h_alg]
    have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := det_fin_two S
    have h_num : (S 0 0 + (δ : ℂ)) * (S 1 1 + (δ : ℂ)) - S 0 1 * S 1 0 = (δ : ℂ) * ((T : ℂ) + 2 * (δ : ℂ)) := by
      rw [← h_trS]
      linear_combination h_detS - h_detS_val
    rw [h_num, ← hτC_sq]
    exact mul_div_cancel_right₀ (δ : ℂ) hτC_sq_ne_zero
  let P_inv : Matrix (Fin 2) (Fin 2) ℂ :=
    !![((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 0 0), -((δ * τ : ℝ) : ℂ)⁻¹ * S 0 1;
       -((δ * τ : ℝ) : ℂ)⁻¹ * S 1 0, ((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 1 1)]
  have h_δτ2_ne : (δ : ℂ) * (τ : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hδ_pos) hτC_sq_ne_zero
  have h_inv_mul : (τ : ℂ)⁻¹ * ((δ * τ : ℝ) : ℂ)⁻¹ = ((δ : ℂ) * (τ : ℂ) ^ 2)⁻¹ := by
    push_cast
    rw [mul_inv, mul_inv, sq, mul_inv]
    ring
  have hP_inv_mul : P * P_inv = 1 := by
    rw [mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp
      have h_alg : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * (((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 0 0)) +
          ((τ : ℂ)⁻¹ * S 0 1) * (-((δ * τ : ℝ) : ℂ)⁻¹ * S 1 0) =
          ((S 0 0 + (δ : ℂ)) * (S 1 1 + (δ : ℂ)) - S 0 1 * S 1 0) / ((δ : ℂ) * (τ : ℂ) ^ 2) := by
        have : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * (((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 0 0)) +
            ((τ : ℂ)⁻¹ * S 0 1) * (-((δ * τ : ℝ) : ℂ)⁻¹ * S 1 0) =
            ((S 0 0 + (δ : ℂ)) * ((T : ℂ) + (δ : ℂ) - S 0 0) - S 0 1 * S 1 0) * ((τ : ℂ)⁻¹ * ((δ * τ : ℝ) : ℂ)⁻¹) := by ring
        rw [this, h_inv_mul, div_eq_mul_inv]
        have h_eq : (T : ℂ) + (δ : ℂ) - S 0 0 = S 1 1 + (δ : ℂ) := by
          rw [← h_trS]
          ring
        rw [h_eq]
      rw [h_alg]
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := det_fin_two S
      have h_num : (S 0 0 + (δ : ℂ)) * (S 1 1 + (δ : ℂ)) - S 0 1 * S 1 0 = (δ : ℂ) * ((T : ℂ) + 2 * (δ : ℂ)) := by
        rw [← h_trS]
        linear_combination h_detS - h_detS_val
      rw [h_num, ← hτC_sq]
      exact div_self h_δτ2_ne
    · dsimp
      have : ((τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ))) * (-((δ * τ : ℝ) : ℂ)⁻¹ * S 0 1) +
          ((τ : ℂ)⁻¹ * S 0 1) * (((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 1 1)) =
          (-(S 0 0 + (δ : ℂ)) * S 0 1 + S 0 1 * ((T : ℂ) + (δ : ℂ) - S 1 1)) * ((τ : ℂ)⁻¹ * ((δ * τ : ℝ) : ℂ)⁻¹) := by ring
      rw [this]
      have h_sub : -(S 0 0 + (δ : ℂ)) * S 0 1 + S 0 1 * ((T : ℂ) + (δ : ℂ) - S 1 1) = 0 := by
        rw [← h_trS]
        ring
      rw [h_sub, zero_mul]
    · dsimp
      have : ((τ : ℂ)⁻¹ * S 1 0) * (((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 0 0)) +
          ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) * (-((δ * τ : ℝ) : ℂ)⁻¹ * S 1 0) =
          (S 1 0 * ((T : ℂ) + (δ : ℂ) - S 0 0) - (S 1 1 + (δ : ℂ)) * S 1 0) * ((τ : ℂ)⁻¹ * ((δ * τ : ℝ) : ℂ)⁻¹) := by ring
      rw [this]
      have h_sub : S 1 0 * ((T : ℂ) + (δ : ℂ) - S 0 0) - (S 1 1 + (δ : ℂ)) * S 1 0 = 0 := by
        rw [← h_trS]
        ring
      rw [h_sub, zero_mul]
    · dsimp
      have h_alg : ((τ : ℂ)⁻¹ * S 1 0) * (-((δ * τ : ℝ) : ℂ)⁻¹ * S 0 1) +
          ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) * (((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 1 1)) =
          ((S 0 0 + (δ : ℂ)) * (S 1 1 + (δ : ℂ)) - S 0 1 * S 1 0) / ((δ : ℂ) * (τ : ℂ) ^ 2) := by
        have : ((τ : ℂ)⁻¹ * S 1 0) * (-((δ * τ : ℝ) : ℂ)⁻¹ * S 0 1) +
            ((τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ))) * (((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 1 1)) =
            ((S 1 1 + (δ : ℂ)) * ((T : ℂ) + (δ : ℂ) - S 1 1) - S 0 1 * S 1 0) * ((τ : ℂ)⁻¹ * ((δ * τ : ℝ) : ℂ)⁻¹) := by ring
        rw [this, h_inv_mul, div_eq_mul_inv]
        have h_eq : (T : ℂ) + (δ : ℂ) - S 1 1 = S 0 0 + (δ : ℂ) := by
          rw [← h_trS]
          ring
        rw [h_eq]
        ring_nf
      rw [h_alg]
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := det_fin_two S
      have h_num : (S 0 0 + (δ : ℂ)) * (S 1 1 + (δ : ℂ)) - S 0 1 * S 1 0 = (δ : ℂ) * ((T : ℂ) + 2 * (δ : ℂ)) := by
        rw [← h_trS]
        linear_combination h_detS - h_detS_val
      rw [h_num, ← hτC_sq]
      exact div_self h_δτ2_ne
  have hP_inv_P : P_inv * P = 1 := by
    rw [mul_eq_one_comm]
    exact hP_inv_mul
  let U := M * P_inv
  have hU_P : M = U * P := by
    dsimp [U]
    rw [Matrix.mul_assoc, hP_inv_P, Matrix.mul_one]
  have hP_inv_symm : P_invᴴ = P_inv := by
    change (!![((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 0 0), -((δ * τ : ℝ) : ℂ)⁻¹ * S 0 1;
              -((δ * τ : ℝ) : ℂ)⁻¹ * S 1 0, ((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 1 1)]ᴴ : Matrix (Fin 2) (Fin 2) ℂ) =
            !![((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 0 0), -((δ * τ : ℝ) : ℂ)⁻¹ * S 0 1;
              -((δ * τ : ℝ) : ℂ)⁻¹ * S 1 0, ((δ * τ : ℝ) : ℂ)⁻¹ * ((T : ℂ) + (δ : ℂ) - S 1 1)]
    rw [conjTranspose_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · dsimp
      rw [map_mul, Complex.conj_inv, Complex.conj_ofReal, map_sub, map_add, Complex.conj_ofReal, Complex.conj_ofReal, hS00_conj]
    · dsimp
      rw [map_mul, map_neg, Complex.conj_inv, Complex.conj_ofReal, hS_10_conj]
    · dsimp
      rw [map_mul, map_neg, Complex.conj_inv, Complex.conj_ofReal, hS_01_conj]
    · dsimp
      rw [map_mul, Complex.conj_inv, Complex.conj_ofReal, map_sub, map_add, Complex.conj_ofReal, Complex.conj_ofReal, hS11_conj]
  have hUt_U : Uᴴ * U = 1 := by
    dsimp [U]
    rw [conjTranspose_mul, hP_inv_symm]
    have : P_inv * Mᴴ * (M * P_inv) = P_inv * (Mᴴ * M) * P_inv := by
      repeat rw [Matrix.mul_assoc]
    rw [this, ← hPP]
    have : P_inv * (P * P) * P_inv = (P_inv * P) * (P * P_inv) := by
      repeat rw [Matrix.mul_assoc]
    rw [this, hP_inv_P, hP_inv_mul, mul_one]
  have hU_Ut : U * Uᴴ = 1 := by
    rw [mul_eq_one_comm]
    exact hUt_U
  have hP_pos : ∀ v : Fin 2 → ℂ, v ≠ 0 → 0 < ((star v ⬝ᵥ P.mulVec v).re) := by
    intro v hv
    have hv_sq : 0 < Complex.normSq (v 0) + Complex.normSq (v 1) := by
      by_contra hc
      have h_le : Complex.normSq (v 0) + Complex.normSq (v 1) ≤ 0 := not_lt.mp hc
      have hv0_sq : Complex.normSq (v 0) = 0 := by
        nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
      have hv1_sq : Complex.normSq (v 1) = 0 := by
        nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
      have hv0 : v 0 = 0 := Complex.normSq_eq_zero.mp hv0_sq
      have hv1 : v 1 = 0 := Complex.normSq_eq_zero.mp hv1_sq
      have hv_zero : v = 0 := by
        ext i
        fin_cases i
        · exact hv0
        · exact hv1
      exact hv hv_zero
    let w₀ := M 0 0 * v 0 + M 0 1 * v 1
    let w₁ := M 1 0 * v 0 + M 1 1 * v 1
    have hw₀_conj : conj w₀ = conj (M 0 0) * conj (v 0) + conj (M 0 1) * conj (v 1) := by
      dsimp [w₀]
      simp only [map_add, map_mul]
    have hw₁_conj : conj w₁ = conj (M 1 0) * conj (v 0) + conj (M 1 1) * conj (v 1) := by
      dsimp [w₁]
      simp only [map_add, map_mul]
    have h_star (z : ℂ) : star z = conj z := rfl
    have hw : conj w₀ * w₀ + conj w₁ * w₁ =
        conj (v 0) * (S 0 0 * v 0 + S 0 1 * v 1) + conj (v 1) * (S 1 0 * v 0 + S 1 1 * v 1) := by
      rw [hw₀_conj, hw₁_conj]
      dsimp [w₀, w₁, S]
      simp only [mul_apply, Fin.sum_univ_two, conjTranspose_apply, h_star]
      ring
    have h_w_re : conj w₀ * w₀ + conj w₁ * w₁ = ((Complex.normSq w₀ + Complex.normSq w₁ : ℝ) : ℂ) := by
      rw [conj_mul_self_eq_normSq, conj_mul_self_eq_normSq]
      push_cast
      rfl
    have h_v_re : conj (v 0) * v 0 + conj (v 1) * v 1 = ((Complex.normSq (v 0) + Complex.normSq (v 1) : ℝ) : ℂ) := by
      rw [conj_mul_self_eq_normSq, conj_mul_self_eq_normSq]
      push_cast
      rfl
    have hP00 : P 0 0 = (τ : ℂ)⁻¹ * (S 0 0 + (δ : ℂ)) := rfl
    have hP01 : P 0 1 = (τ : ℂ)⁻¹ * S 0 1 := rfl
    have hP10 : P 1 0 = (τ : ℂ)⁻¹ * S 1 0 := rfl
    have hP11 : P 1 1 = (τ : ℂ)⁻¹ * (S 1 1 + (δ : ℂ)) := rfl
    have h_dot_expand : star v ⬝ᵥ P.mulVec v =
        conj (v 0) * (P 0 0 * v 0 + P 0 1 * v 1) + conj (v 1) * (P 1 0 * v 0 + P 1 1 * v 1) := by
      simp [dotProduct, mulVec, Fin.sum_univ_two]
    have h_dot : star v ⬝ᵥ P.mulVec v =
        (τ : ℂ)⁻¹ * (((conj (v 0) * (S 0 0 * v 0 + S 0 1 * v 1) +
                       conj (v 1) * (S 1 0 * v 0 + S 1 1 * v 1))) +
          (δ : ℂ) * (conj (v 0) * v 0 + conj (v 1) * v 1)) := by
      rw [h_dot_expand, hP00, hP01, hP10, hP11]
      ring
    rw [h_dot, ← hw, h_w_re, h_v_re]
    have h_real_cast : (τ : ℂ)⁻¹ * (((Complex.normSq w₀ + Complex.normSq w₁ : ℝ) : ℂ) +
        (δ : ℂ) * ((Complex.normSq (v 0) + Complex.normSq (v 1) : ℝ) : ℂ)) =
        ((τ⁻¹ * (Complex.normSq w₀ + Complex.normSq w₁ + δ * (Complex.normSq (v 0) + Complex.normSq (v 1))) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h_real_cast, Complex.ofReal_re]
    have h_inner : 0 < Complex.normSq w₀ + Complex.normSq w₁ + δ * (Complex.normSq (v 0) + Complex.normSq (v 1)) := by
      have hw_nonneg : 0 ≤ Complex.normSq w₀ + Complex.normSq w₁ :=
        add_nonneg (Complex.normSq_nonneg w₀) (Complex.normSq_nonneg w₁)
      have hδv_pos : 0 < δ * (Complex.normSq (v 0) + Complex.normSq (v 1)) := mul_pos hδ_pos hv_sq
      linarith
    exact mul_pos (inv_pos.mpr hτ_pos) h_inner
  exact ⟨U, P, hU_P, hUt_U, hU_Ut, hP_symm, hPP, hP_det, hP_pos⟩

/-- Uniqueness of the GL(2, ℂ) unitary polar decomposition. -/
theorem gl2_complex_polar_decomposition_unique
    (M U₁ P₁ U₂ P₂ : Matrix (Fin 2) (Fin 2) ℂ) (δ τ : ℂ) (hτ : τ ≠ 0)
    (h_fact₁ : M = U₁ * P₁) (h_fact₂ : M = U₂ * P₂)
    (hPP₁ : P₁ * P₁ = Mᴴ * M) (hPP₂ : P₂ * P₂ = Mᴴ * M)
    (hdet₁ : P₁.det = δ) (hdet₂ : P₂.det = δ)
    (htr₁ : P₁ 0 0 + P₁ 1 1 = τ) (htr₂ : P₂ 0 0 + P₂ 1 1 = τ)
    (P_inv : Matrix (Fin 2) (Fin 2) ℂ) (hP_inv : P₁ * P_inv = 1) :
    P₁ = P₂ ∧ U₁ = U₂ := by
  have hP_eq : P₁ = P₂ :=
    gl2_complex_polar_P_unique_of_cayley_hamilton P₁ P₂ (Mᴴ * M) δ τ hτ hPP₁ hPP₂ hdet₁ hdet₂ htr₁ htr₂
  have hU_eq : U₁ = U₂ := by
    have hM : U₁ * P₁ = U₂ * P₁ := by
      rw [← h_fact₁, h_fact₂, ← hP_eq]
    calc U₁
      _ = U₁ * 1 := by rw [Matrix.mul_one]
      _ = U₁ * (P₁ * P_inv) := by rw [hP_inv]
      _ = (U₁ * P₁) * P_inv := by rw [Matrix.mul_assoc]
      _ = (U₂ * P₁) * P_inv := by rw [hM]
      _ = U₂ * (P₁ * P_inv) := by rw [Matrix.mul_assoc]
      _ = U₂ * 1 := by rw [hP_inv]
      _ = U₂ := by rw [Matrix.mul_one]
  exact ⟨hP_eq, hU_eq⟩

/-- Left unitary equivariance for GL(2, ℂ) polar decomposition:
    If U is unitary and G is unitary, then G * M = (G * U) * P,
    with G * U unitary and Gram matrix preserved. -/
theorem hyperbolic_polar_left_unitary_equivariance
    (U P G : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : Uᴴ * U = 1) (hG : Gᴴ * G = 1) :
    let M := U * P
    G * M = (G * U) * P ∧
    (G * U)ᴴ * (G * U) = 1 ∧
    (G * M)ᴴ * (G * M) = Mᴴ * M := by
  intro M
  have h_fact : G * M = (G * U) * P := by
    dsimp [M]
    rw [Matrix.mul_assoc]
  have h_U : (G * U)ᴴ * (G * U) = 1 := by
    rw [conjTranspose_mul]
    calc Uᴴ * Gᴴ * (G * U)
      _ = Uᴴ * (Gᴴ * G) * U := by
        repeat rw [Matrix.mul_assoc]
      _ = Uᴴ * 1 * U := by
        rw [hG]
      _ = Uᴴ * U := by
        rw [Matrix.mul_one]
      _ = 1 := hU
  have h_Gram : (G * M)ᴴ * (G * M) = Mᴴ * M := by
    rw [conjTranspose_mul]
    calc Mᴴ * Gᴴ * (G * M)
      _ = Mᴴ * (Gᴴ * G) * M := by
        repeat rw [Matrix.mul_assoc]
      _ = Mᴴ * 1 * M := by
        rw [hG]
      _ = Mᴴ * M := by
        rw [Matrix.mul_one]
  exact ⟨h_fact, h_U, h_Gram⟩

/-- Unitary conjugation equivariance for GL(2, ℂ) polar decomposition:
    If U is unitary, P is Hermitian, and G is unitary,
    then G * M * Gᴴ = (G * U * Gᴴ) * (G * P * Gᴴ) preserves the polar structure. -/
theorem hyperbolic_polar_conjugation_equivariance
    (U P G : Matrix (Fin 2) (Fin 2) ℂ)
    (hU_left : Uᴴ * U = 1) (hU_right : U * Uᴴ = 1)
    (hP : Pᴴ = P)
    (hG_left : Gᴴ * G = 1) (hG_right : G * Gᴴ = 1) :
    let M := U * P
    let U_G := G * U * Gᴴ
    let P_G := G * P * Gᴴ
    let M_G := G * M * Gᴴ
    M_G = U_G * P_G ∧
    U_Gᴴ * U_G = 1 ∧
    U_G * U_Gᴴ = 1 ∧
    P_Gᴴ = P_G ∧
    M_Gᴴ * M_G = P_G * P_G := by
  intro M U_G P_G M_G
  have h_fact : M_G = U_G * P_G := by
    dsimp [M_G, U_G, P_G, M]
    calc G * (U * P) * Gᴴ
      _ = (G * U) * P * Gᴴ := by
        repeat rw [Matrix.mul_assoc]
      _ = (G * U) * 1 * P * Gᴴ := by
        rw [Matrix.mul_one]
      _ = (G * U) * (Gᴴ * G) * P * Gᴴ := by
        rw [hG_left]
      _ = ((G * U * Gᴴ) * G) * P * Gᴴ := by
        repeat rw [Matrix.mul_assoc]
      _ = (G * U * Gᴴ) * (G * P * Gᴴ) := by
        repeat rw [Matrix.mul_assoc]
  have h_U_left : U_Gᴴ * U_G = 1 := by
    dsimp [U_G]
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc G * (Uᴴ * Gᴴ) * (G * U * Gᴴ)
      _ = G * Uᴴ * (Gᴴ * G) * U * Gᴴ := by
        repeat rw [Matrix.mul_assoc]
      _ = G * Uᴴ * 1 * U * Gᴴ := by
        rw [hG_left]
      _ = G * (Uᴴ * U) * Gᴴ := by
        rw [Matrix.mul_one]
        repeat rw [Matrix.mul_assoc]
      _ = G * 1 * Gᴴ := by
        rw [hU_left]
      _ = G * Gᴴ := by
        rw [Matrix.mul_one]
      _ = 1 := hG_right
  have h_U_right : U_G * U_Gᴴ = 1 := by
    dsimp [U_G]
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc G * U * Gᴴ * (G * (Uᴴ * Gᴴ))
      _ = G * U * (Gᴴ * G) * Uᴴ * Gᴴ := by
        repeat rw [Matrix.mul_assoc]
      _ = G * U * 1 * Uᴴ * Gᴴ := by
        rw [hG_left]
      _ = G * (U * Uᴴ) * Gᴴ := by
        rw [Matrix.mul_one]
        repeat rw [Matrix.mul_assoc]
      _ = G * 1 * Gᴴ := by
        rw [hU_right]
      _ = G * Gᴴ := by
        rw [Matrix.mul_one]
      _ = 1 := hG_right
  have h_P_self : P_Gᴴ = P_G := by
    dsimp [P_G]
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP]
    rw [Matrix.mul_assoc]
  have h_PP : M_Gᴴ * M_G = P_G * P_G := by
    rw [h_fact]
    calc (U_G * P_G)ᴴ * (U_G * P_G)
      _ = P_Gᴴ * U_Gᴴ * (U_G * P_G) := by
        rw [conjTranspose_mul]
      _ = P_Gᴴ * (U_Gᴴ * U_G) * P_G := by
        repeat rw [Matrix.mul_assoc]
      _ = P_Gᴴ * 1 * P_G := by
        rw [h_U_left]
      _ = P_Gᴴ * P_G := by
        rw [Matrix.mul_one]
      _ = P_G * P_G := by
        rw [h_P_self]
  exact ⟨h_fact, h_U_left, h_U_right, h_P_self, h_PP⟩

end InfoGeometry.Algebra.ComplexSL2IwasawaAndHyperbolicPolar

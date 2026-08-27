/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.QuantumAlgebra.G2ArtinLift

/-!
# $G_2$ Artin-Hecke Cyclotomic Lift and Cartan Plane Coxeter Representation

This module formalizes the exact algebraic 2D Cartan representation of the $I_2(6)$ Artin group
and its spin/cyclotomic lift over any commutative ring $K$ containing a 12th cyclotomic root $\zeta$.

Key Theorems:
1. 🏆 `root3_alg_sq_eq_three`: Exact algebraic identity $(\zeta + \zeta^{-1})^2 = 3$ whenever $\Phi_{12}(\zeta) = 0$.
2. 🏆 `g2_artin_braid_relation_cartan`: Exact 6-term Artin braid relation $(B_s B_\ell)^3 = (B_\ell B_s)^3 = -I$.
3. 🏆 `coxeter_cartan_pow_three`: Classical Cartan Coxeter reflection product satisfies $(B_s B_\ell)^3 = -I$.
4. 🏆 `cartan_coxeter_pow_six`: Classical Cartan Coxeter reflection product has order 6: $(B_s B_\ell)^6 = I$.
5. 🏆 `spin_coxeter_cartan_pow_six`: The $\zeta$-twisted spin Coxeter operator $C_{\text{spin}} = \zeta \cdot (B_s B_\ell)$ satisfies $C_{\text{spin}}^6 = -I$.
6. 🏆 `spin_coxeter_cartan_pow_twelve`: Exact 12-fold cyclotomic closure $C_{\text{spin}}^{12} = I$.
-/

variable {K : Type*} [CommRing K]

/-- The algebraic $\sqrt{3}$ defined as $\zeta + \zeta^{-1}$. -/
def root3_alg (zeta zeta_inv : K) : K := zeta + zeta_inv

/-- 🏆 THEOREM 1: Exact algebraic identity $(\zeta + \zeta^{-1})^2 = 3$ for roots of $\Phi_{12}(X) = X^4 - X^2 + 1$. -/
theorem root3_alg_sq_eq_three
    (zeta zeta_inv : K)
    (h_inv : zeta * zeta_inv = 1)
    (h_phi12 : zeta ^ 4 - zeta ^ 2 + 1 = 0) :
    (root3_alg zeta zeta_inv) ^ 2 = 3 := by
  dsimp [root3_alg]
  have h_exp : (zeta + zeta_inv) ^ 2 - 3 = (zeta_inv ^ 2) * (zeta ^ 4 - zeta ^ 2 + 1) := by
    have h1 : (zeta + zeta_inv) ^ 2 - 3 = zeta ^ 2 + zeta_inv ^ 2 - 1 := by
      calc
        (zeta + zeta_inv) ^ 2 - 3 = zeta ^ 2 + 2 * (zeta * zeta_inv) + zeta_inv ^ 2 - 3 := by ring
        _ = zeta ^ 2 + 2 * 1 + zeta_inv ^ 2 - 3 := by rw [h_inv]
        _ = zeta ^ 2 + zeta_inv ^ 2 - 1 := by ring
    have h2 : (zeta_inv ^ 2) * (zeta ^ 4 - zeta ^ 2 + 1) = zeta ^ 2 + zeta_inv ^ 2 - 1 := by
      calc
        (zeta_inv ^ 2) * (zeta ^ 4 - zeta ^ 2 + 1) =
            (zeta * zeta_inv) ^ 2 * zeta ^ 2 - (zeta * zeta_inv) ^ 2 + zeta_inv ^ 2 := by ring
        _ = 1 ^ 2 * zeta ^ 2 - 1 ^ 2 + zeta_inv ^ 2 := by rw [h_inv]
        _ = zeta ^ 2 + zeta_inv ^ 2 - 1 := by ring
    rw [h1, ← h2]
  have h_zero : (zeta + zeta_inv) ^ 2 - 3 = 0 := by
    rw [h_exp, h_phi12, mul_zero]
  exact sub_eq_zero.mp h_zero

/-- 2D Cartan simple root reflection $B_s$. -/
def BsCartan (r3 : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![-1, r3],
    ![0, 1]]

/-- 2D Cartan simple root reflection $B_\ell$. -/
def BlCartan (r3 : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![1, 0],
    ![r3, -1]]

/-- Classical Cartan Coxeter matrix $C = B_s B_\ell$. -/
def CoxeterCartan (r3 : K) : Matrix (Fin 2) (Fin 2) K :=
  BsCartan r3 * BlCartan r3

theorem Bs_mul_Bl (r3 : K) (hr3 : r3 ^ 2 = 3) :
    BsCartan r3 * BlCartan r3 = ![![2, -r3], ![r3, -1]] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      -1 + r3 * r3 = -1 + r3 ^ 2 := by ring
      _ = -1 + 3 := by rw [hr3]
      _ = 2 := by ring
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Bl_mul_Bs (r3 : K) (hr3 : r3 ^ 2 = 3) :
    BlCartan r3 * BsCartan r3 = ![![-1, r3], ![-r3, 2]] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [BsCartan, BlCartan, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      r3 * r3 + -1 = r3 ^ 2 - 1 := by ring
      _ = 3 - 1 := by rw [hr3]
      _ = 2 := by ring

theorem coxeter_cartan_sq (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (CoxeterCartan r3) ^ 2 = ![![1, -r3], ![r3, -2]] := by
  dsimp [CoxeterCartan]
  rw [sq, Bs_mul_Bl r3 hr3]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      2 * 2 + -(r3 * r3) = 4 - r3 ^ 2 := by ring
      _ = 4 - 3 := by rw [hr3]
      _ = 1 := by ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      -(r3 * r3) + 1 = -(r3 ^ 2) + 1 := by ring
      _ = -3 + 1 := by rw [hr3]
      _ = -2 := by ring

/-- 🏆 THEOREM 2: Exact cube of the Coxeter matrix is $-I$: $(B_s B_\ell)^3 = -I$. -/
theorem coxeter_cartan_pow_three (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (CoxeterCartan r3) ^ 3 = -1 := by
  have h3 : (CoxeterCartan r3) ^ 3 = (CoxeterCartan r3) ^ 2 * CoxeterCartan r3 := by
    calc
      (CoxeterCartan r3) ^ 3 = (CoxeterCartan r3) ^ (2 + 1) := rfl
      _ = (CoxeterCartan r3) ^ 2 * (CoxeterCartan r3) ^ 1 := by rw [pow_add]
      _ = _ := by rw [pow_one]
  change (CoxeterCartan r3) ^ 3 = -1
  rw [h3, coxeter_cartan_sq r3 hr3]
  dsimp [CoxeterCartan]
  rw [Bs_mul_Bl r3 hr3]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      2 + -(r3 * r3) = 2 - r3 ^ 2 := by ring
      _ = 2 - 3 := by rw [hr3]
      _ = -1 := by ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      -(r3 * r3) + 2 = -(r3 ^ 2) + 2 := by ring
      _ = -3 + 2 := by rw [hr3]
      _ = -1 := by ring

theorem bl_bs_sq (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (BlCartan r3 * BsCartan r3) ^ 2 = ![![ -2, r3], ![-r3, 1]] := by
  rw [sq, Bl_mul_Bs r3 hr3]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      1 + -(r3 * r3) = 1 - r3 ^ 2 := by ring
      _ = 1 - 3 := by rw [hr3]
      _ = -2 := by ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      -(r3 * r3) + 2 * 2 = -(r3 ^ 2) + 4 := by ring
      _ = -3 + 4 := by rw [hr3]
      _ = 1 := by ring

theorem bl_bs_pow_three (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (BlCartan r3 * BsCartan r3) ^ 3 = -1 := by
  have h3 : (BlCartan r3 * BsCartan r3) ^ 3 = (BlCartan r3 * BsCartan r3) ^ 2 * (BlCartan r3 * BsCartan r3) := by
    calc
      (BlCartan r3 * BsCartan r3) ^ 3 = (BlCartan r3 * BsCartan r3) ^ (2 + 1) := rfl
      _ = (BlCartan r3 * BsCartan r3) ^ 2 * (BlCartan r3 * BsCartan r3) ^ 1 := by rw [pow_add]
      _ = _ := by rw [pow_one]
  rw [h3, bl_bs_sq r3 hr3, Bl_mul_Bs r3 hr3]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      2 + -(r3 * r3) = 2 - r3 ^ 2 := by ring
      _ = 2 - 3 := by rw [hr3]
      _ = -1 := by ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      -(r3 * r3) + 2 = -(r3 ^ 2) + 2 := by ring
      _ = -3 + 2 := by rw [hr3]
      _ = -1 := by ring

/-- 🏆 THEOREM 3: Exact 6-term Artin braid relation $(B_s B_\ell)^3 = (B_\ell B_s)^3 = -I$. -/
theorem g2_artin_braid_relation_cartan (r3 : K) (hr3 : r3 ^ 2 = 3) :
    BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 =
      BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 := by
  have h1 : BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 =
      (BsCartan r3 * BlCartan r3) ^ 3 := by
    calc
      BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 =
          ((BsCartan r3 * BlCartan r3) * (BsCartan r3 * BlCartan r3)) * (BsCartan r3 * BlCartan r3) := by
        simp only [mul_assoc]
      _ = (BsCartan r3 * BlCartan r3) ^ 2 * (BsCartan r3 * BlCartan r3) := by rw [sq]
      _ = (BsCartan r3 * BlCartan r3) ^ 3 := by
        calc
          (BsCartan r3 * BlCartan r3) ^ 2 * (BsCartan r3 * BlCartan r3) =
              (BsCartan r3 * BlCartan r3) ^ 2 * (BsCartan r3 * BlCartan r3) ^ 1 := by rw [pow_one]
          _ = (BsCartan r3 * BlCartan r3) ^ (2 + 1) := by rw [← pow_add]
          _ = (BsCartan r3 * BlCartan r3) ^ 3 := rfl
  have h2 : BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 =
      (BlCartan r3 * BsCartan r3) ^ 3 := by
    calc
      BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 * BlCartan r3 * BsCartan r3 =
          ((BlCartan r3 * BsCartan r3) * (BlCartan r3 * BsCartan r3)) * (BlCartan r3 * BsCartan r3) := by
        simp only [mul_assoc]
      _ = (BlCartan r3 * BsCartan r3) ^ 2 * (BlCartan r3 * BsCartan r3) := by rw [sq]
      _ = (BlCartan r3 * BsCartan r3) ^ 3 := by
        calc
          (BlCartan r3 * BsCartan r3) ^ 2 * (BlCartan r3 * BsCartan r3) =
              (BlCartan r3 * BsCartan r3) ^ 2 * (BlCartan r3 * BsCartan r3) ^ 1 := by rw [pow_one]
          _ = (BlCartan r3 * BsCartan r3) ^ (2 + 1) := by rw [← pow_add]
          _ = (BlCartan r3 * BsCartan r3) ^ 3 := rfl
  have h_c3 : (BsCartan r3 * BlCartan r3) ^ 3 = -1 := coxeter_cartan_pow_three r3 hr3
  rw [h1, h2, h_c3, bl_bs_pow_three r3 hr3]

/-- 🏆 THEOREM 4: Classical Cartan Coxeter reflection product has order 6: $(B_s B_\ell)^6 = I$. -/
theorem cartan_coxeter_pow_six (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (CoxeterCartan r3) ^ 6 = 1 := by
  have h6 : (CoxeterCartan r3) ^ 6 = ((CoxeterCartan r3) ^ 3) ^ 2 := by
    have h_mul : (3 : ℕ) * 2 = 6 := rfl
    rw [← pow_mul, h_mul]
  rw [h6, coxeter_cartan_pow_three r3 hr3]
  have h_neg_sq : (-1 : Matrix (Fin 2) (Fin 2) K) ^ 2 = 1 := by
    rw [sq, neg_mul_neg, mul_one]
  exact h_neg_sq

/-- 🏆 THEOREM 5: The $\zeta$-twisted spin Coxeter operator $C_{\text{spin}} = \zeta \cdot (B_s B_\ell)$ satisfies $C_{\text{spin}}^6 = -I$. -/
theorem spin_coxeter_cartan_pow_six
    (r3 zeta : K) (hr3 : r3 ^ 2 = 3) (h_zeta6 : zeta ^ 6 = -1) :
    (zeta • CoxeterCartan r3) ^ 6 = -1 := by
  rw [smul_pow, cartan_coxeter_pow_six r3 hr3, h_zeta6]
  rw [neg_one_smul]

/-- 🏆 THEOREM 6: Exact 12-fold cyclotomic closure $C_{\text{spin}}^{12} = I$. -/
theorem spin_coxeter_cartan_pow_twelve
    (r3 zeta : K) (hr3 : r3 ^ 2 = 3) (h_zeta6 : zeta ^ 6 = -1) :
    (zeta • CoxeterCartan r3) ^ 12 = 1 := by
  have h12 : (zeta • CoxeterCartan r3) ^ 12 = ((zeta • CoxeterCartan r3) ^ 6) ^ 2 := by
    have h_mul : (6 : ℕ) * 2 = 12 := rfl
    rw [← pow_mul, h_mul]
  rw [h12, spin_coxeter_cartan_pow_six r3 zeta hr3 h_zeta6]
  have h_neg_sq : (-1 : Matrix (Fin 2) (Fin 2) K) ^ 2 = 1 := by
    rw [sq, neg_mul_neg, mul_one]
  exact h_neg_sq

end InfoGeometry.QuantumAlgebra.G2ArtinLift

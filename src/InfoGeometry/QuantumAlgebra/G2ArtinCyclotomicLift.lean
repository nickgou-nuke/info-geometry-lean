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

variable {K : Type*} [Ring K]

/-- The algebraic $\sqrt{3}$ defined as $\zeta + \zeta^{-1}$. -/
def root3_alg (zeta zeta_inv : K) : K := zeta + zeta_inv

/-- 🏆 THEOREM 1: Exact algebraic identity $(\zeta + \zeta^{-1})^2 = 3$ for roots of $\Phi_{12}(X) = X^4 - X^2 + 1$
    over any non-commutative ring `[Ring K]`. -/
theorem root3_alg_sq_eq_three
    (zeta zeta_inv : K)
    (h_inv : zeta * zeta_inv = 1)
    (h_phi12 : zeta ^ 4 - zeta ^ 2 + 1 = 0) :
    (root3_alg zeta zeta_inv) ^ 2 = 3 := by
  dsimp [root3_alg]
  have h_zeta_inv : zeta_inv = zeta - zeta ^ 3 := by
    have h_id : zeta_inv - (zeta - zeta ^ 3) =
        (zeta ^ 4 - zeta ^ 2 + 1) * zeta_inv + (zeta - zeta ^ 3) * (zeta * zeta_inv - 1) := by
      noncomm_ring
    rw [h_phi12, zero_mul, zero_add, h_inv, sub_self, mul_zero] at h_id
    exact sub_eq_zero.mp h_id
  rw [h_zeta_inv]
  have h_exp : (zeta + (zeta - zeta ^ 3)) ^ 2 - 3 = (zeta ^ 2 - 3) * (zeta ^ 4 - zeta ^ 2 + 1) := by
    noncomm_ring
  have h_zero : (zeta + (zeta - zeta ^ 3)) ^ 2 - 3 = 0 := by
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

/-! A concrete scalar phase lift of the two Artin generators.  The phase is
placed on one generator; the two sides of the six-term relation contain the
same number of occurrences of that generator. -/

def BsSpin (zeta r3 : K) : Matrix (Fin 2) (Fin 2) K :=
  zeta • BsCartan r3

def BlSpin (r3 : K) : Matrix (Fin 2) (Fin 2) K :=
  BlCartan r3

theorem Bs_mul_Bl (r3 : K) (hr3 : r3 ^ 2 = 3) :
    BsCartan r3 * BlCartan r3 = ![![2, -r3], ![r3, -1]] := by
  have hr3' : r3 * r3 = 3 := by rw [← sq, hr3]
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    rw [hr3']; norm_num
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    noncomm_ring

theorem Bl_mul_Bs (r3 : K) (hr3 : r3 ^ 2 = 3) :
    BlCartan r3 * BsCartan r3 = ![![-1, r3], ![-r3, 2]] := by
  have hr3' : r3 * r3 = 3 := by rw [← sq, hr3]
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [BsCartan, BlCartan]
    rw [hr3']; norm_num

/-- Explicit square of the Coxeter matrix $C^2 = (B_s B_\ell)^2$. -/
def CoxeterCartanSq (r3 : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![1, -r3],
    ![r3, -2]]

theorem coxeter_cartan_sq (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (CoxeterCartan r3) ^ 2 = CoxeterCartanSq r3 := by
  have hr3' : r3 * r3 = 3 := by rw [← sq, hr3]
  have hsq : (CoxeterCartan r3) ^ 2 = CoxeterCartan r3 * CoxeterCartan r3 := pow_two _
  refine hsq.trans ?_
  have hC : CoxeterCartan r3 = ![![2, -r3], ![r3, -1]] := Bs_mul_Bl r3 hr3
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC]
    dsimp [CoxeterCartanSq]
    rw [neg_mul, hr3']; norm_num
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC]
    dsimp [CoxeterCartanSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC]
    dsimp [CoxeterCartanSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC]
    dsimp [CoxeterCartanSq]
    rw [mul_neg, hr3']; norm_num

/-- 🏆 THEOREM 2: Exact cube of the Coxeter matrix is $-I$: $(B_s B_\ell)^3 = -I$. -/
theorem coxeter_cartan_pow_three (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (CoxeterCartan r3) ^ 3 = (-1 : Matrix (Fin 2) (Fin 2) K) := by
  have hr3' : r3 * r3 = 3 := by rw [← sq, hr3]
  have h3 : (CoxeterCartan r3) ^ 3 = (CoxeterCartan r3) ^ 2 * CoxeterCartan r3 := by
    rw [pow_succ]
  refine h3.trans ?_
  rw [coxeter_cartan_sq r3 hr3]
  have hC : CoxeterCartan r3 = ![![2, -r3], ![r3, -1]] := Bs_mul_Bl r3 hr3
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC, Matrix.neg_apply, Matrix.one_apply]
    dsimp [CoxeterCartanSq]
    rw [neg_mul, hr3']; norm_num
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC, Matrix.neg_apply, Matrix.one_apply]
    dsimp [CoxeterCartanSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC, Matrix.neg_apply, Matrix.one_apply]
    dsimp [CoxeterCartanSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hC, Matrix.neg_apply, Matrix.one_apply]
    dsimp [CoxeterCartanSq]
    rw [mul_neg, hr3']; norm_num

/-- Explicit square of the reverse Cartan product $(B_\ell B_s)^2$. -/
def BlBsSq (r3 : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![-2, r3],
    ![-r3, 1]]

theorem bl_bs_sq (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (BlCartan r3 * BsCartan r3) ^ 2 = BlBsSq r3 := by
  have hr3' : r3 * r3 = 3 := by rw [← sq, hr3]
  have hsq : (BlCartan r3 * BsCartan r3) ^ 2 = (BlCartan r3 * BsCartan r3) * (BlCartan r3 * BsCartan r3) := pow_two _
  refine hsq.trans ?_
  have hB : BlCartan r3 * BsCartan r3 = ![![ -1, r3], ![-r3, 2]] := Bl_mul_Bs r3 hr3
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB]
    dsimp [BlBsSq]
    rw [mul_neg r3 r3, hr3']; norm_num
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB]
    dsimp [BlBsSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB]
    dsimp [BlBsSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB]
    dsimp [BlBsSq]
    rw [neg_mul, hr3']; norm_num

theorem bl_bs_pow_three (r3 : K) (hr3 : r3 ^ 2 = 3) :
    (BlCartan r3 * BsCartan r3) ^ 3 = (-1 : Matrix (Fin 2) (Fin 2) K) := by
  have hr3' : r3 * r3 = 3 := by rw [← sq, hr3]
  have h3 : (BlCartan r3 * BsCartan r3) ^ 3 = (BlCartan r3 * BsCartan r3) ^ 2 * (BlCartan r3 * BsCartan r3) := by
    rw [pow_succ]
  refine h3.trans ?_
  rw [bl_bs_sq r3 hr3]
  have hB : BlCartan r3 * BsCartan r3 = ![![ -1, r3], ![-r3, 2]] := Bl_mul_Bs r3 hr3
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB, Matrix.neg_apply, Matrix.one_apply]
    dsimp [BlBsSq]
    rw [mul_neg r3 r3, hr3']; norm_num
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB, Matrix.neg_apply, Matrix.one_apply]
    dsimp [BlBsSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB, Matrix.neg_apply, Matrix.one_apply]
    dsimp [BlBsSq]
    noncomm_ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two, hB, Matrix.neg_apply, Matrix.one_apply]
    dsimp [BlBsSq]
    rw [neg_mul, hr3']; norm_num

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
      _ = (BsCartan r3 * BlCartan r3) ^ 2 * (BsCartan r3 * BlCartan r3) := by rw [pow_two]
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
      _ = (BlCartan r3 * BsCartan r3) ^ 2 * (BlCartan r3 * BsCartan r3) := by rw [pow_two]
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
    rw [pow_two, neg_mul_neg, mul_one]
  exact h_neg_sq

/-- 🏆 THEOREM 5: The $\zeta$-twisted spin Coxeter operator $C_{\text{spin}} = \zeta \cdot (B_s B_\ell)$ satisfies $C_{\text{spin}}^6 = -I$. -/
theorem spin_coxeter_cartan_pow_six {K : Type*} [CommRing K]
    (r3 zeta : K) (hr3 : r3 ^ 2 = 3) (h_zeta6 : zeta ^ 6 = -1) :
    (zeta • CoxeterCartan r3) ^ 6 = -1 := by
  rw [smul_pow, cartan_coxeter_pow_six r3 hr3, h_zeta6]
  rw [neg_one_smul]

/-- 🏆 THEOREM 6: Exact 12-fold cyclotomic closure $C_{\text{spin}}^{12} = I$. -/
theorem spin_coxeter_cartan_pow_twelve {K : Type*} [CommRing K]
    (r3 zeta : K) (hr3 : r3 ^ 2 = 3) (h_zeta6 : zeta ^ 6 = -1) :
    (zeta • CoxeterCartan r3) ^ 12 = 1 := by
  have h12 : (zeta • CoxeterCartan r3) ^ 12 = ((zeta • CoxeterCartan r3) ^ 6) ^ 2 := by
    have h_mul : (6 : ℕ) * 2 = 12 := rfl
    rw [← pow_mul, h_mul]
  rw [h12, spin_coxeter_cartan_pow_six r3 zeta hr3 h_zeta6]
  have h_neg_sq : (-1 : Matrix (Fin 2) (Fin 2) K) ^ 2 = 1 := by
    rw [sq, neg_mul_neg, mul_one]
  exact h_neg_sq

/-- The scalar-twisted generators satisfy the same Artin relation. -/
theorem g2_artin_braid_relation_spin {K : Type*} [CommRing K]
    (r3 zeta : K) (hr3 : r3 ^ 2 = 3) :
    BsSpin zeta r3 * BlSpin r3 * BsSpin zeta r3 * BlSpin r3 *
        BsSpin zeta r3 * BlSpin r3 =
      BlSpin r3 * BsSpin zeta r3 * BlSpin r3 * BsSpin zeta r3 *
        BlSpin r3 * BsSpin zeta r3 := by
  simp only [BsSpin, BlSpin, Matrix.smul_mul, Matrix.mul_smul]
  rw [g2_artin_braid_relation_cartan r3 hr3]

/-- The product of the phase-compatible generators is the phase-twisted
    Cartan Coxeter operator used by the spin readback. -/
theorem spin_generators_product
    (r3 zeta : K) :
    BsSpin zeta r3 * BlSpin r3 = zeta • CoxeterCartan r3 := by
  simp [BsSpin, BlSpin, CoxeterCartan]

/-- Concrete Coxeter defect for the phase-compatible Artin generators. -/
theorem spin_generators_coxeter_pow_six {K : Type*} [CommRing K]
    (r3 zeta : K) (hr3 : r3 ^ 2 = 3) (h_zeta6 : zeta ^ 6 = -1) :
    (BsSpin zeta r3 * BlSpin r3) ^ 6 = -1 := by
  rw [spin_generators_product]
  exact spin_coxeter_cartan_pow_six r3 zeta hr3 h_zeta6

/-- Twelvefold closure for the same concrete phase-compatible lift. -/
theorem spin_generators_coxeter_pow_twelve {K : Type*} [CommRing K]
    (r3 zeta : K) (hr3 : r3 ^ 2 = 3) (h_zeta6 : zeta ^ 6 = -1) :
    (BsSpin zeta r3 * BlSpin r3) ^ 12 = 1 := by
  rw [spin_generators_product]
  exact spin_coxeter_cartan_pow_twelve r3 zeta hr3 h_zeta6

end InfoGeometry.QuantumAlgebra.G2ArtinLift

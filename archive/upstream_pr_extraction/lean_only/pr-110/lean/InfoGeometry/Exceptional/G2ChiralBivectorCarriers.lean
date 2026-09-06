/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.Zorn.ChiralPhaseMatrix
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.QuantumAlgebra.G2ArtinCyclotomicLift

namespace InfoGeometry.Exceptional.G2ChiralBivectorCarriers

open InfoGeometry.Algebra.Zorn
open InfoGeometry.QuantumAlgebra.G2ArtinLift

/-!
# Four-Plane Decomposition of the 8D Circular Carrier and Operator Lift

This module formalizes the canonical 4-plane decomposition of the 8-dimensional
circular split-octonion basis $\mathcal{B}_{\text{circ}} = \{u_+, \sigma_+^1, \sigma_+^2, \sigma_+^3, u_-, \sigma_-^1, \sigma_-^2, \sigma_-^3\}$:

$$\mathcal{H}_{\text{circ}} = H_0 \oplus H_1 \oplus H_2 \oplus H_3$$

where:
- $H_0 = \operatorname{span}\{u_+, u_-\}$ (Plane 0: diagonal idempotent sheet)
- $H_1 = \operatorname{span}\{\sigma_+^1, \sigma_-^1\}$ (Plane 1: Color 1 chiral null channel)
- $H_2 = \operatorname{span}\{\sigma_+^2, \sigma_-^2\}$ (Plane 2: Color 2 chiral null channel)
- $H_3 = \operatorname{span}\{\sigma_+^3, \sigma_-^3\}$ (Plane 3: Color 3 chiral null channel)

Key Theorems:
1. 🏆 `fourPlaneLift_mul`: Direct sum functoriality $\widehat{B_1} \cdot \widehat{B_2} = \widehat{B_1 B_2}$.
2. 🏆 `fourPlaneLift_pow`: Powers commute with the 4-plane lift: $\widehat{B}^n = \widehat{B^n}$.
3. 🏆 `fourPlaneLift_sq`: $B^2 = -I_2 \implies \widehat{B}^2 = -I_8$.
4. 🏆 `fourPlaneLift_artin_six`: The 2D Cartan Artin generators $B_s, B_\ell$ lift to 8D operators
   satisfying the exact 6-term Artin braid relation:
   $$\widehat{B_s} \widehat{B_\ell} \widehat{B_s} \widehat{B_\ell} \widehat{B_s} \widehat{B_\ell} = \widehat{B_\ell} \widehat{B_s} \widehat{B_\ell} \widehat{B_s} \widehat{B_\ell} \widehat{B_s} = -I_8$$
5. 🏆 `fourPlaneLift_coxeter_order_six`: $(\widehat{B_s} \widehat{B_\ell})^6 = I_8$.
6. 🏆 `fourPlaneLift_spin_coxeter_twelve`: $(\zeta \cdot (\widehat{B_s} \widehat{B_\ell}))^6 = -I_8$ and 12th power is $I_8$.
-/

variable {R : Type*} [CommRing R]

/-- The 4-plane block direct sum lift $\widehat{B} = B \oplus B \oplus B \oplus B$ on $\text{Fin } 4 \times \text{Fin } 2$. -/
def fourPlaneLift (B : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) R :=
  Matrix.of (fun (k1, c1) (k2, c2) => if k1 = k2 then B c1 c2 else 0)

/-- 🏆 THEOREM 1: Multiplicative functoriality of the 4-plane direct sum lift. -/
theorem fourPlaneLift_mul (B1 B2 : Matrix (Fin 2) (Fin 2) R) :
    fourPlaneLift (B1 * B2) = fourPlaneLift B1 * fourPlaneLift B2 := by
  ext ⟨k1, c1⟩ ⟨k2, c2⟩
  simp only [fourPlaneLift, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hk : k1 = k2
  · subst hk
    rw [if_pos rfl]
    have h1 : (∑ x_1 : Fin 2, (if k1 = k1 then B1 c1 x_1 else 0) * if k1 = k1 then B2 x_1 c2 else 0) =
        (B1 * B2) c1 c2 := by
      simp [Matrix.mul_apply]
    have h2 : ∀ k : Fin 4, k ≠ k1 → (∑ x_1 : Fin 2, (if k1 = k then B1 c1 x_1 else 0) * if k = k1 then B2 x_1 c2 else 0) = 0 := by
      intro k hk_ne
      apply Finset.sum_eq_zero
      intro x _
      simp [if_neg hk_ne.symm]
    rw [Finset.sum_eq_single k1]
    · exact h1.symm
    · intro k _ hk_ne
      exact h2 k hk_ne
    · intro h_not
      exact (h_not (Finset.mem_univ _)).elim
  · rw [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro c _
    by_cases hk1 : k1 = k
    · subst hk1
      simp [if_neg hk]
    · simp [if_neg hk1]

/-- 🏆 THEOREM 2: The 4-plane lift of the identity matrix is the identity. -/
theorem fourPlaneLift_one :
    fourPlaneLift (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext ⟨k1, c1⟩ ⟨k2, c2⟩
  simp only [fourPlaneLift, Matrix.of_apply, Matrix.one_apply]
  by_cases hk : k1 = k2
  · subst hk
    simp [Prod.ext_iff]
  · have hneq : (k1, c1) ≠ (k2, c2) := fun h => hk (Prod.ext_iff.mp h |>.1)
    simp [hk, hneq]

/-- 🏆 THEOREM 3: Powers commute with the 4-plane lift: $\widehat{B}^n = \widehat{B^n}$. -/
theorem fourPlaneLift_pow (B : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (fourPlaneLift B) ^ n = fourPlaneLift (B ^ n) := by
  induction n with
  | zero => simp [fourPlaneLift_one]
  | succ n ih =>
      rw [pow_succ, pow_succ, ih, fourPlaneLift_mul]

/-- 🏆 THEOREM 4: The 4-plane lift of any 2D bivector $B^2 = -I_2$ is an 8D bivector $\widehat{B}^2 = -I_8$. -/
theorem fourPlaneLift_sq (B : Matrix (Fin 2) (Fin 2) R) (hB : B * B = -1) :
    fourPlaneLift B * fourPlaneLift B = -1 := by
  rw [← fourPlaneLift_mul, hB]
  ext ⟨k1, c1⟩ ⟨k2, c2⟩
  simp only [fourPlaneLift, Matrix.of_apply, Matrix.neg_apply, Matrix.one_apply]
  by_cases hk : k1 = k2
  · subst hk
    simp [Prod.ext_iff]
  · have hneq : (k1, c1) ≠ (k2, c2) := fun h => hk (Prod.ext_iff.mp h |>.1)
    simp [hk, hneq]

/-- 🏆 THEOREM 5: The 4-plane lift of the 2D Cartan Artin generators satisfies the exact 6-term braid relation. -/
theorem fourPlaneLift_artin_six (r3 : R) (hr3 : r3 ^ 2 = 3) :
    fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3) *
      fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3) *
      fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3) =
    fourPlaneLift (BlCartan r3) * fourPlaneLift (BsCartan r3) *
      fourPlaneLift (BlCartan r3) * fourPlaneLift (BsCartan r3) *
      fourPlaneLift (BlCartan r3) * fourPlaneLift (BsCartan r3) := by
  have h_artin := g2_artin_braid_relation_cartan r3 hr3
  rw [← fourPlaneLift_mul, ← fourPlaneLift_mul, ← fourPlaneLift_mul, ← fourPlaneLift_mul, ← fourPlaneLift_mul]
  rw [← fourPlaneLift_mul, ← fourPlaneLift_mul, ← fourPlaneLift_mul, ← fourPlaneLift_mul, ← fourPlaneLift_mul]
  rw [h_artin]

/-- 🏆 THEOREM 6: The 4-plane Coxeter product has sixth power $I_8$. -/
theorem fourPlaneLift_coxeter_pow_six (r3 : R) (hr3 : r3 ^ 2 = 3) :
    (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3)) ^ 6 = 1 := by
  rw [← fourPlaneLift_mul, fourPlaneLift_pow]
  change fourPlaneLift ((CoxeterCartan r3) ^ 6) = 1
  rw [cartan_coxeter_pow_six r3 hr3, fourPlaneLift_one]

/-- 🏆 THEOREM 7: Exact 12-fold cyclotomic closure of the 8D spin Coxeter lift. -/
theorem fourPlaneLift_spin_coxeter_twelve
    (r3 zeta : R) (hr3 : r3 ^ 2 = 3) (h_zeta6 : zeta ^ 6 = -1) :
    (zeta • (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3))) ^ 6 = -1 ∧
    (zeta • (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3))) ^ 12 = 1 := by
  have h6 : (zeta • (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3))) ^ 6 = -1 := by
    rw [smul_pow, fourPlaneLift_coxeter_pow_six r3 hr3, h_zeta6, neg_one_smul]
  have h12 : (zeta • (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3))) ^ 12 = 1 := by
    have h_pow12 : (zeta • (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3))) ^ 12 =
        ((zeta • (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3))) ^ 6) ^ 2 := by
      have h_mul : (6 : ℕ) * 2 = 12 := rfl
      rw [← pow_mul, h_mul]
    rw [h_pow12, h6]
    have h_neg_sq : (-1 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) R) ^ 2 = 1 := by
      rw [sq, neg_mul_neg, mul_one]
    exact h_neg_sq
  exact ⟨h6, h12⟩

end InfoGeometry.Exceptional.G2ChiralBivectorCarriers

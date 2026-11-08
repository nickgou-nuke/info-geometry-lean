/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Carrier Master Finite Algebraic Lemmas & Projector Idempotency Capstone

This capstone formally integrates all core finite algebraic lemmas across the
carrier infrastructure of the repository:

1. **Krein Carrier Fundamental Projector Algebra**:
   - Indefinite inner product carrier $V = V_+ \oplus V_-$ with projectors $P_+, P_-$.
   - $P_+ + P_- = 1$, $P_+ P_- = P_- P_+ = 0$, $P_\pm^2 = P_\pm$.
   - The fundamental symmetry $J = P_+ - P_-$ squares to 1: $J^2 = 1$.

2. **Split-Clifford Chiral Carrier Involutions**:
   - For any bivector involution $B^2 = 1$, the chiral projectors satisfy:
     $(1 + B)(1 - B) = 0$ and $(1 + B) + (1 - B) = 2 \cdot 1$.

3. **Jordan-Wigner CAR Number Operator Idempotency**:
   - For fermionic creation/annihilation operators $\{c, c^\dagger\} = 1$ with $c^2 = (c^\dagger)^2 = 0$,
     the number operator $N = c^\dagger c$ is idempotent: $N^2 = N$.

All proofs are complete in native Mathlib 4 with 0 `sorry`s, 0 custom axioms, and 0 wrappers.
-/

open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

namespace InfoGeometry.Canonical.CarrierMasterLemmas

/-! ## 1. Krein Carrier Fundamental Projector Algebra -/

/-- Krein carrier projectors $P_+, P_-$ and fundamental symmetry $J = P_+ - P_-$. -/
structure KreinCarrierProjectorData (A : Type*) [Ring A] where
  P_plus : A
  P_minus : A
  sum_id : P_plus + P_minus = 1
  ortho : P_plus * P_minus = 0
  ortho_rev : P_minus * P_plus = 0
  idem_plus : P_plus * P_plus = P_plus
  idem_minus : P_minus * P_minus = P_minus

/-- 🏆 THEOREM 1: Fundamental symmetry $J = P_+ - P_-$ squares to 1: $J^2 = 1$. -/
theorem krein_fundamental_symmetry_sq {A : Type*} [Ring A] (D : KreinCarrierProjectorData A) :
    (D.P_plus - D.P_minus) * (D.P_plus - D.P_minus) = 1 := by
  have h_exp : (D.P_plus - D.P_minus) * (D.P_plus - D.P_minus) =
               D.P_plus * D.P_plus - D.P_plus * D.P_minus - D.P_minus * D.P_plus + D.P_minus * D.P_minus := by
    noncomm_ring
  rw [h_exp, D.idem_plus, D.idem_minus, D.ortho, D.ortho_rev]
  calc
    D.P_plus - 0 - 0 + D.P_minus = D.P_plus + D.P_minus := by
      rw [sub_zero, sub_zero]
    _ = 1 := D.sum_id

/-! ## 2. Split-Clifford Chiral Carrier Projectors -/

/-- 🏆 THEOREM 2: Chiral Projector Orthogonality $(1 + B)(1 - B) = 0$ when $B^2 = 1$. -/
theorem chiral_projector_ortho {A : Type*} [Ring A] (B : A) (hB : B * B = 1) :
    (1 + B) * (1 - B) = 0 := by
  calc
    (1 + B) * (1 - B) = 1 - B * B := by noncomm_ring
    _ = 1 - 1 := by rw [hB]
    _ = 0 := sub_self 1

/-- 🏆 THEOREM 3: Chiral Projector Sum $(1 + B) + (1 - B) = 2 \cdot 1$. -/
theorem chiral_projector_sum {A : Type*} [Ring A] (B : A) :
    (1 + B) + (1 - B) = 1 + 1 := by
  calc
    (1 + B) + (1 - B) = 1 + B + 1 - B := by rw [add_sub_assoc]
    _ = 1 + 1 + B - B := by rw [add_right_comm (1 : A) B 1]
    _ = 1 + 1 := by rw [add_sub_cancel_right]

/-! ## 3. Jordan-Wigner CAR Number Operator Idempotency -/

/-- CAR fermionic creation/annihilation carrier pair. -/
structure CARCarrierPair (A : Type*) [Ring A] where
  c : A
  c_dag : A
  anticomm : c * c_dag + c_dag * c = 1
  nilpotent : c * c = 0
  nilpotent_dag : c_dag * c_dag = 0

/-- 🏆 THEOREM 4: The fermionic number operator $N = c^\dagger c$ is idempotent: $N^2 = N$. -/
theorem car_number_operator_idempotent {A : Type*} [Ring A] (C : CARCarrierPair A) :
    (C.c_dag * C.c) * (C.c_dag * C.c) = C.c_dag * C.c := by
  have h_comm : C.c * C.c_dag = 1 - C.c_dag * C.c := by
    rw [← C.anticomm, add_sub_cancel_right]
  calc
    (C.c_dag * C.c) * (C.c_dag * C.c) = C.c_dag * (C.c * C.c_dag) * C.c := by
      simp only [mul_assoc]
    _ = C.c_dag * (1 - C.c_dag * C.c) * C.c := by
      rw [h_comm]
    _ = (C.c_dag * 1 - C.c_dag * (C.c_dag * C.c)) * C.c := by
      rw [mul_sub]
    _ = (C.c_dag - (C.c_dag * C.c_dag) * C.c) * C.c := by
      simp only [mul_one, mul_assoc]
    _ = (C.c_dag - 0 * C.c) * C.c := by
      rw [C.nilpotent_dag]
    _ = C.c_dag * C.c := by
      simp only [zero_mul, sub_zero]

/-! ## 4. Master Synthesis Theorem -/

/--
🏆 **MASTER CARRIER ALGEBRAIC LEMMAS SYNTHESIS**

Unifies:
1. **Krein Fundamental Symmetry**: $(P_+ - P_-)^2 = 1$.
2. **Chiral Projector Orthogonality**: $(1 + B)(1 - B) = 0$.
3. **Chiral Projector Sum**: $(1 + B) + (1 - B) = 2$.
4. **CAR Number Operator Idempotency**: $(c^\dagger c)^2 = c^\dagger c$.
5. **Yang-Baxter Topological Integrability**: $F \cdot B \cdot F = R$ and $F^2 = 1$.
-/
theorem grand_carrier_algebraic_lemmas_synthesis
    {A : Type*} [Ring A] (D : KreinCarrierProjectorData A)
    (B_op : A) (hB : B_op * B_op = 1)
    (C : CARCarrierPair A) :
    ((D.P_plus - D.P_minus) * (D.P_plus - D.P_minus) = 1) ∧
    ((1 + B_op) * (1 - B_op) = 0) ∧
    ((1 + B_op) + (1 - B_op) = 1 + 1) ∧
    ((C.c_dag * C.c) * (C.c_dag * C.c) = C.c_dag * C.c) ∧
    (F * F = 1) ∧
    (F * B * F = R) :=
  ⟨krein_fundamental_symmetry_sq D,
   chiral_projector_ortho B_op hB,
   chiral_projector_sum B_op,
   car_number_operator_idempotent C,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.CarrierMasterLemmas

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.Z2ProjectorWeights

/-! # Klein twisting in a noncommutative operator algebra

Use the existing involution projectors to construct `P₊ - j P₋`. The phase
`j` is an operator with square `-1`; its required commutation relations are
explicit. Thus the result also applies to real operator algebras carrying an
internal complex structure. In a complex algebra one may take `j = i • 1`.

The algebraic involution at the end is not identified with a Tomita modular
conjugation. No represented local algebra or analytic continuation is assumed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KleinTwist

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The Klein phase, with the convention `P₊ - j P₋`. -/
def twist (Γ j : A) : A := projectorPlus Γ - j * projectorMinus Γ

private theorem commute_plus (Γ j : A) (h : Commute j Γ) :
    Commute j (projectorPlus Γ) := by
  change j * projectorPlus Γ = projectorPlus Γ * j
  simp only [projectorPlus, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    mul_one, one_mul, h.eq]

private theorem commute_minus (Γ j : A) (h : Commute j Γ) :
    Commute j (projectorMinus Γ) := by
  change j * projectorMinus Γ = projectorMinus Γ * j
  simp only [projectorMinus, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul,
    mul_one, one_mul, h.eq]

/-- Ordered phase multiplication uses the existing four projector product laws.
Only the right phase must commute with the grading. -/
theorem twist_mul (Γ j k : A) (hΓ : Γ * Γ = 1) (hk : Commute k Γ) :
    twist Γ j * twist Γ k = projectorPlus Γ + (j * k) * projectorMinus Γ := by
  have hp := (commute_plus Γ k hk).symm
  have hq := (commute_minus Γ k hk).symm
  have hpk : projectorPlus Γ * (k * projectorMinus Γ) = 0 := by
    rw [hp.left_comm, projectorPlus_mul_projectorMinus Γ hΓ, mul_zero]
  have hqk : (j * projectorMinus Γ) * (k * projectorMinus Γ) =
      (j * k) * projectorMinus Γ := by
    rw [hq.mul_mul_mul_comm, projectorMinus_mul_projectorMinus Γ hΓ]
  unfold twist
  rw [sub_mul, mul_sub, mul_sub, projectorPlus_mul_projectorPlus Γ hΓ, hpk,
    mul_assoc j (projectorMinus Γ) (projectorPlus Γ),
    projectorMinus_mul_projectorPlus Γ hΓ, mul_zero, hqk]
  abel

/-- The square is the statistics grading, with no commutative-algebra assumption. -/
theorem twist_sq (Γ j : A) (hΓ : Γ * Γ = 1) (hj : j * j = -1)
    (hjΓ : Commute j Γ) : twist Γ j * twist Γ j = Γ := by
  rw [twist_mul Γ j j hΓ hjΓ, hj]
  simpa [projectorWeight] using projectorWeight_one_neg_one Γ

/-- Division-free version of `(1 + i Γ) / (1 + i)`: multiplication by
`1 + j` recovers the numerator with the order of factors explicit. -/
theorem twist_mul_one_add_phase (Γ j : A) (hj : j * j = -1)
    (hjΓ : Commute j Γ) : twist Γ j * (1 + j) = 1 + j * Γ := by
  have hp := (commute_plus Γ j hjΓ).eq
  have hq := (commute_minus Γ j hjΓ).eq
  have hdiff : projectorPlus Γ - projectorMinus Γ = Γ := by
    simpa [projectorWeight, sub_eq_add_neg] using projectorWeight_one_neg_one Γ
  calc
    twist Γ j * (1 + j) =
        projectorPlus Γ + projectorMinus Γ + j * (projectorPlus Γ - projectorMinus Γ) := by
      unfold twist
      rw [mul_add, mul_one, sub_mul, hp.symm,
        mul_assoc j (projectorMinus Γ) j, hq.symm,
        ← mul_assoc j j (projectorMinus Γ), hj]
      noncomm_ring
    _ = 1 + j * Γ := by rw [projectorPlus_add_projectorMinus, hdiff]

/-- Negating the phase gives a right inverse. -/
theorem twist_mul_neg_phase (Γ j : A) (hΓ : Γ * Γ = 1) (hj : j * j = -1)
    (hjΓ : Commute j Γ) : twist Γ j * twist Γ (-j) = 1 := by
  rw [twist_mul Γ j (-j) hΓ hjΓ.neg_left, mul_neg, hj, neg_neg, one_mul]
  exact projectorPlus_add_projectorMinus Γ

/-- Negating the phase also gives a left inverse. -/
theorem twist_neg_phase_mul (Γ j : A) (hΓ : Γ * Γ = 1) (hj : j * j = -1)
    (hjΓ : Commute j Γ) : twist Γ (-j) * twist Γ j = 1 := by
  rw [twist_mul Γ (-j) j hΓ hjΓ, neg_mul, hj, neg_neg, one_mul]
  exact projectorPlus_add_projectorMinus Γ

theorem twist_fourth (Γ j : A) (hΓ : Γ * Γ = 1) (hj : j * j = -1)
    (hjΓ : Commute j Γ) : twist Γ j ^ 4 = 1 := by
  calc
    twist Γ j ^ 4 = (twist Γ j * twist Γ j) * (twist Γ j * twist Γ j) := by
      noncomm_ring
    _ = Γ * Γ := by rw [twist_sq Γ j hΓ hj hjΓ]
    _ = 1 := hΓ

/-- Exact order four needs a nontrivial grading; the fourth-power law alone does not. -/
theorem orderOf_twist (Γ j : A) (hΓ : Γ * Γ = 1) (hj : j * j = -1)
    (hjΓ : Commute j Γ) (hne : Γ ≠ 1) : orderOf (twist Γ j) = 4 := by
  have htwo : twist Γ j ^ 2 ≠ 1 := by
    simpa [pow_two, twist_sq Γ j hΓ hj hjΓ] using hne
  exact orderOf_eq_prime_pow (p := 2) (n := 1) htwo (twist_fourth Γ j hΓ hj hjΓ)

@[simp] theorem twist_one (j : A) : twist 1 j = 1 := by
  simp [twist, projectorPlus, projectorMinus]
  module

private theorem plus_mul_odd (Γ C : A) (hC : Γ * C = -(C * Γ)) :
    projectorPlus Γ * C = C * projectorMinus Γ := by
  simp only [projectorPlus, projectorMinus, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [add_mul, mul_sub, one_mul, mul_one, hC, sub_eq_add_neg]

private theorem minus_mul_odd (Γ C : A) (hC : Γ * C = -(C * Γ)) :
    projectorMinus Γ * C = C * projectorPlus Γ := by
  simp only [projectorPlus, projectorMinus, smul_mul_assoc, mul_smul_comm]
  congr 1
  simp only [sub_mul, mul_add, one_mul, mul_one, hC, sub_neg_eq_add]

/-- Opposite-phase twisting of an odd operator produces `j Γ C`.
The phase commutes with this operator; the grading anticommutes with it.
When `j² = -1`, the opposite-phase factor is the inverse, as proved above. -/
theorem twist_odd (Γ j C : A) (hΓ : Γ * Γ = 1)
    (hjΓ : Commute j Γ) (hjC : Commute j C) (hC : Γ * C = -(C * Γ)) :
    twist Γ j * C * twist Γ (-j) = j * Γ * C := by
  have hp := plus_mul_odd Γ C hC
  have hq := minus_mul_odd Γ C hC
  have hswap : twist Γ j * C = C * (projectorMinus Γ - j * projectorPlus Γ) := by
    simp only [twist, sub_mul, mul_assoc, hp, hq, mul_sub]
    rw [hjC.left_comm]
  have hqp : projectorMinus Γ * (j * projectorMinus Γ) = j * projectorMinus Γ := by
    rw [(commute_minus Γ j hjΓ).symm.left_comm,
      projectorMinus_mul_projectorMinus Γ hΓ]
  have hpp : (j * projectorPlus Γ) * projectorPlus Γ = j * projectorPlus Γ := by
    rw [mul_assoc, projectorPlus_mul_projectorPlus Γ hΓ]
  have hpq : (j * projectorPlus Γ) * (j * projectorMinus Γ) = 0 := by
    rw [(commute_plus Γ j hjΓ).symm.mul_mul_mul_comm,
      projectorPlus_mul_projectorMinus Γ hΓ, mul_zero]
  have hprod : (projectorMinus Γ - j * projectorPlus Γ) * twist Γ (-j) = -j * Γ := by
    unfold twist
    simp only [neg_mul, sub_neg_eq_add, sub_mul, mul_add]
    rw [projectorMinus_mul_projectorPlus Γ hΓ, hqp, hpp, hpq]
    have hdiff : projectorPlus Γ - projectorMinus Γ = Γ := by
      simpa [projectorWeight, sub_eq_add_neg] using projectorWeight_one_neg_one Γ
    calc
      0 - j * projectorPlus Γ + (j * projectorMinus Γ - 0) =
          -(j * (projectorPlus Γ - projectorMinus Γ)) := by noncomm_ring
      _ = -(j * Γ) := by rw [hdiff]
  rw [hswap, mul_assoc, hprod]
  calc
    C * (-j * Γ) = -j * (C * Γ) := by
      rw [← mul_assoc, mul_neg, hjC.eq.symm]
      noncomm_ring
    _ = j * Γ * C := by rw [neg_mul, ← mul_neg, ← hC, ← mul_assoc]

/-- Exact ordered commutator/anticommutator conversion for two odd operators. -/
theorem twisted_commutator (Γ j A₁ C : A) (hΓ : Γ * Γ = 1)
    (hjΓ : Commute j Γ) (hjA : Commute j A₁) (hjC : Commute j C)
    (hA : Γ * A₁ = -(A₁ * Γ)) (hC : Γ * C = -(C * Γ)) :
    A₁ * (twist Γ j * C * twist Γ (-j)) - (twist Γ j * C * twist Γ (-j)) * A₁ =
      -j * Γ * (A₁ * C + C * A₁) := by
  rw [twist_odd Γ j C hΓ hjΓ hjC hC]
  have hAΓ : A₁ * Γ = -(Γ * A₁) := by rw [hA, neg_neg]
  calc
    A₁ * (j * Γ * C) - j * Γ * C * A₁ =
        j * (A₁ * Γ) * C - j * Γ * C * A₁ := by
          rw [mul_assoc j Γ C, hjA.symm.left_comm]
          noncomm_ring
    _ = -j * Γ * (A₁ * C + C * A₁) := by rw [hAΓ]; noncomm_ring

/-- The twist turns graded locality into ordinary commutation, in both directions. -/
theorem twisted_commute_iff (Γ j A₁ C : A) (hΓ : Γ * Γ = 1) (hj : j * j = -1)
    (hjΓ : Commute j Γ) (hjA : Commute j A₁) (hjC : Commute j C)
    (hA : Γ * A₁ = -(A₁ * Γ)) (hC : Γ * C = -(C * Γ)) :
    Commute A₁ (twist Γ j * C * twist Γ (-j)) ↔ A₁ * C + C * A₁ = 0 := by
  change _ = _ ↔ _
  rw [← sub_eq_zero, twisted_commutator Γ j A₁ C hΓ hjΓ hjA hjC hA hC]
  have hinv : (Γ * j) * (-j * Γ) = 1 := by
    calc
      (Γ * j) * (-j * Γ) = -(Γ * (j * j) * Γ) := by noncomm_ring
      _ = 1 := by rw [hj]; simpa using hΓ
  constructor
  · intro h
    calc
      A₁ * C + C * A₁ = ((Γ * j) * (-j * Γ)) * (A₁ * C + C * A₁) := by
        rw [hinv, one_mul]
      _ = (Γ * j) * ((-j * Γ) * (A₁ * C + C * A₁)) := mul_assoc _ _ _
      _ = 0 := by rw [h, mul_zero]
  · intro h
    rw [h, mul_zero]

/-- A conjugation that fixes the grading and reverses the phase reverses the twist. -/
theorem map_twist (φ : A →ₐ[ℚ] A) (Γ j : A) (hΓ : φ Γ = Γ) (hj : φ j = -j) :
    φ (twist Γ j) = twist Γ (-j) := by
  simp [twist, projectorPlus, projectorMinus, hΓ, hj]

section Star

variable [StarRing A]

/-- The algebraic inverse is the adjoint for self-adjoint grading and skew-adjoint phase. -/
theorem star_twist (Γ j : A) (hΓ : star Γ = Γ) (hj : star j = -j)
    (hjΓ : Commute j Γ) : star (twist Γ j) = twist Γ (-j) := by
  have hq := (commute_minus Γ j hjΓ).eq
  simp only [twist, star_sub, star_mul]
  have hp : star (projectorPlus Γ) = projectorPlus Γ := by
    simp [projectorPlus, hΓ]
  have hm : star (projectorMinus Γ) = projectorMinus Γ := by
    simp [projectorMinus, hΓ]
  rw [hp, hm, hj, mul_neg, neg_mul, hq]

/-- Native unitary membership, proved from the two inverse laws. -/
theorem twist_mem_unitary (Γ j : A) (hΓ : Γ * Γ = 1) (hj : j * j = -1)
    (hjΓ : Commute j Γ) (hΓs : star Γ = Γ) (hjs : star j = -j) :
    twist Γ j ∈ unitary A := by
  rw [Unitary.mem_iff, star_twist Γ j hΓs hjs hjΓ]
  exact ⟨twist_neg_phase_mul Γ j hΓ hj hjΓ, twist_mul_neg_phase Γ j hΓ hj hjΓ⟩

end Star

section SignCancellation

variable {M : Type*} [Monoid M]

/-- Commuting square roots of the same involution already have involutive product. -/
theorem commuting_square_roots_involutive (T U Γ : M) (hTU : Commute T U)
    (hT : T * T = Γ) (hU : U * U = Γ) (hΓ : Γ * Γ = 1) :
    (T * U) * (T * U) = 1 := by
  rw [hTU.symm.mul_mul_mul_comm, hT, hU, hΓ]

/-- Additional phase intertwining preserves that involutivity. This is an
algebraic theorem, not a construction of analytic modular conjugation. -/
theorem twisted_product_involutive (Z Zinv T U Γ : M)
    (hTU : Commute T U) (hT : T * T = Γ) (hU : U * U = Γ) (hΓ : Γ * Γ = 1)
    (hUZ : Commute U Z) (hTZ : T * Z = Zinv * T) (hZZ : Z * Zinv = 1) :
    (Z * T * U) * (Z * T * U) = 1 := by
  have hinter : (T * U) * Z = Zinv * (T * U) := by
    rw [mul_assoc, hUZ.eq, ← mul_assoc T Z U, hTZ, mul_assoc]
  calc
    (Z * T * U) * (Z * T * U) = Z * ((T * U) * Z) * (T * U) := by
      simp only [mul_assoc]
    _ = (Z * Zinv) * ((T * U) * (T * U)) := by rw [hinter]; simp only [mul_assoc]
    _ = 1 := by rw [hZZ, commuting_square_roots_involutive T U Γ hTU hT hU hΓ, one_mul]

end SignCancellation

end InfoGeometry.OperatorAlgebra.KleinTwist

end

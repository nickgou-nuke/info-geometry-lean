/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinCommutant

/-!
# Additive and reverse-order laws for the Drazin inverse

Ring-level results over an arbitrary (noncommutative) associative unital ring `R`,
stated for the canonical predicate
`IsDrazinInverse a b k ↔ a * b = b * a ∧ b * a * b = b ∧ a ^ (k + 1) * b = a ^ k`.

1. **Drazin's orthogonal additive theorem (Drazin 1958).** If `a * b = 0` and
   `b * a = 0`, `a'` is a Drazin inverse of `a` of index `k` and `b'` one of `b` of
   index `l`, then `a' + b'` is a Drazin inverse of `a + b` of index `max (max k l) 1`.
   (The lower bound `1` is needed: at index `0` the power law would read
   `(a + b) * (a' + b') = 1`.)
2. **Reverse-order law for commuting elements.** If `a * b = b * a`, then
   `b' * a'` is a Drazin inverse of `a * b` of index `max k l`, and `b' * a' = a' * b'`.

The commuting reverse-order law relies on the bicommutant property
`DrazinCommutant.inverse_commutes_of_commutes` (a Drazin inverse commutes with
every element commuting with `a`).  No commutativity of `R` is assumed.

Not covered here: the general commuting additive formula of Hartwig–Wang–Wei,
which requires the Drazin inverse of `1 + a' * b`.
-/

namespace InfoGeometry.Canonical.DrazinAdditiveReverseOrder

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.DrazinCommutant

variable {R : Type*} [Ring R]

section Basic

variable {a a' : R} {k : ℕ}

/-- A Drazin inverse factors as `a' = a' * a' * a`. -/
theorem drazin_eq_sq_mul (h : IsDrazinInverse a a' k) : a' = a' * a' * a := by
  calc
    a' = a' * a * a' := h.idempotent.symm
    _ = a' * (a * a') := by rw [mul_assoc]
    _ = a' * (a' * a) := by rw [h.comm]
    _ = a' * a' * a := by rw [mul_assoc]

/-- A Drazin inverse factors as `a' = a * a' * a'`. -/
theorem drazin_eq_mul_sq (h : IsDrazinInverse a a' k) : a' = a * a' * a' := by
  calc
    a' = a' * a * a' := h.idempotent.symm
    _ = a * a' * a' := by rw [← h.comm]

end Basic

/-! ## 1. Drazin's orthogonal additive theorem -/

section Orthogonal

variable {a b a' b' : R} {k l : ℕ}

/-- If `a * b = 0` and `b * a = 0` then `(a + b) ^ (n + 1) = a ^ (n + 1) + b ^ (n + 1)`. -/
theorem add_pow_succ_of_orthogonal (hab : a * b = 0) (hba : b * a = 0) (n : ℕ) :
    (a + b) ^ (n + 1) = a ^ (n + 1) + b ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : a ^ (n + 1) * b = 0 := by rw [pow_succ, mul_assoc, hab, mul_zero]
      have h2 : b ^ (n + 1) * a = 0 := by rw [pow_succ, mul_assoc, hba, mul_zero]
      calc
        (a + b) ^ (n + 1 + 1) = (a ^ (n + 1) + b ^ (n + 1)) * (a + b) := by
          rw [pow_succ, ih]
        _ = a ^ (n + 1) * a + a ^ (n + 1) * b + (b ^ (n + 1) * a + b ^ (n + 1) * b) := by
          noncomm_ring
        _ = a ^ (n + 1 + 1) + b ^ (n + 1 + 1) := by
          rw [h1, h2, ← pow_succ, ← pow_succ]; abel

/-- Under `a * b = 0`, the Drazin inverse of `a` is left-annihilated by `b`:
`b * a' = 0`. -/
theorem mul_drazin_eq_zero_of_mul_eq_zero (ha : IsDrazinInverse a a' k) (hba : b * a = 0) :
    b * a' = 0 := by
  rw [drazin_eq_mul_sq ha, ← mul_assoc, ← mul_assoc, hba, zero_mul, zero_mul]

/-- Under `a * b = 0`, the Drazin inverse of `a` right-annihilates `b`: `a' * b = 0`. -/
theorem drazin_mul_eq_zero_of_mul_eq_zero (ha : IsDrazinInverse a a' k) (hab : a * b = 0) :
    a' * b = 0 := by
  rw [drazin_eq_sq_mul ha, mul_assoc, hab, mul_zero]

/-- **Drazin's orthogonal additive theorem.**  If `a * b = 0 = b * a`, then the sum of
Drazin inverses is a Drazin inverse of the sum, of index `max (max k l) 1`. -/
theorem isDrazinInverse_add_of_orthogonal
    (ha : IsDrazinInverse a a' k) (hb : IsDrazinInverse b b' l)
    (hab : a * b = 0) (hba : b * a = 0) :
    IsDrazinInverse (a + b) (a' + b') (max (max k l) 1) := by
  -- cross annihilations
  have h_a'b : a' * b = 0 := drazin_mul_eq_zero_of_mul_eq_zero ha hab
  have h_ba' : b * a' = 0 := mul_drazin_eq_zero_of_mul_eq_zero ha hba
  have h_b'a : b' * a = 0 := drazin_mul_eq_zero_of_mul_eq_zero hb hba
  have h_ab' : a * b' = 0 := mul_drazin_eq_zero_of_mul_eq_zero hb hab
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · -- commutation
    calc
      (a + b) * (a' + b') = a * a' + a * b' + (b * a' + b * b') := by noncomm_ring
      _ = a' * a + a' * b + (b' * a + b' * b) := by
        rw [ha.comm, hb.comm, h_ab', h_ba', h_a'b, h_b'a]
      _ = (a' + b') * (a + b) := by noncomm_ring
  · -- outer inverse law
    have h1 : a' * a * b' = 0 := by rw [mul_assoc, h_ab', mul_zero]
    have h2 : b' * b * a' = 0 := by rw [mul_assoc, h_ba', mul_zero]
    have h3 : a' * b * a' = 0 := by rw [h_a'b, zero_mul]
    have h4 : a' * b * b' = 0 := by rw [h_a'b, zero_mul]
    have h5 : b' * a * a' = 0 := by rw [h_b'a, zero_mul]
    have h6 : b' * a * b' = 0 := by rw [h_b'a, zero_mul]
    calc
      (a' + b') * (a + b) * (a' + b')
          = a' * a * a' + a' * a * b' + a' * b * a' + a' * b * b'
            + (b' * a * a' + b' * a * b' + b' * b * a' + b' * b * b') := by noncomm_ring
      _ = a' + b' := by
        rw [ha.idempotent, hb.idempotent, h1, h2, h3, h4, h5, h6]; abel
  · -- power law at index m = max (max k l) 1
    obtain ⟨n, hn⟩ : ∃ n, max (max k l) 1 = n + 1 := ⟨max (max k l) 1 - 1, by omega⟩
    have hk : k ≤ max (max k l) 1 := le_trans (le_max_left k l) (le_max_left _ 1)
    have hl : l ≤ max (max k l) 1 := le_trans (le_max_right k l) (le_max_left _ 1)
    have hpa : a ^ (max (max k l) 1 + 1) * a' = a ^ max (max k l) 1 := ha.power_le hk
    have hpb : b ^ (max (max k l) 1 + 1) * b' = b ^ max (max k l) 1 := hb.power_le hl
    rw [hn] at hpa hpb ⊢
    have hz1 : a ^ (n + 1 + 1) * b' = 0 := by rw [pow_succ, mul_assoc, h_ab', mul_zero]
    have hz2 : b ^ (n + 1 + 1) * a' = 0 := by rw [pow_succ, mul_assoc, h_ba', mul_zero]
    calc
      (a + b) ^ (n + 1 + 1) * (a' + b')
          = (a ^ (n + 1 + 1) + b ^ (n + 1 + 1)) * (a' + b') := by
            rw [add_pow_succ_of_orthogonal hab hba (n + 1)]
      _ = a ^ (n + 1 + 1) * a' + a ^ (n + 1 + 1) * b'
            + (b ^ (n + 1 + 1) * a' + b ^ (n + 1 + 1) * b') := by noncomm_ring
      _ = a ^ (n + 1) + b ^ (n + 1) := by rw [hpa, hpb, hz1, hz2]; abel
      _ = (a + b) ^ (n + 1) := (add_pow_succ_of_orthogonal hab hba n).symm

end Orthogonal

/-! ## 2. Reverse-order law for commuting elements -/

section Commuting

variable {a b a' b' : R} {k l : ℕ}

/-- For commuting `a, b` with Drazin inverses `a', b'`, all four elements pairwise
commute.  This packages the bicommutant property. -/
theorem drazin_pairwise_commute_of_commute
    (ha : IsDrazinInverse a a' k) (hb : IsDrazinInverse b b' l) (hab : a * b = b * a) :
    Commute a' b ∧ Commute b' a ∧ Commute a' b' := by
  have h1 : a' * b = b * a' := inverse_commutes_of_commutes ha b hab
  have h2 : b' * a = a * b' := inverse_commutes_of_commutes hb a hab.symm
  have h3 : a' * b' = b' * a' := inverse_commutes_of_commutes ha b' h2.symm
  exact ⟨h1, h2, h3⟩

/-- **Reverse-order law.**  If `a * b = b * a`, then `b' * a'` is a Drazin inverse of
`a * b` of index `max k l`. -/
theorem isDrazinInverse_mul_of_commute
    (ha : IsDrazinInverse a a' k) (hb : IsDrazinInverse b b' l) (hab : a * b = b * a) :
    IsDrazinInverse (a * b) (b' * a') (max k l) := by
  obtain ⟨hc1, hc2, hc3⟩ := drazin_pairwise_commute_of_commute ha hb hab
  have cab : Commute a b := hab
  have caa' : Commute a a' := ha.comm
  have cbb' : Commute b b' := hb.comm
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · -- `a * b` commutes with `b' * a'`
    have hb'a' : Commute b' (a * b) := hc2.mul_right cbb'.symm
    have ha'ab : Commute a' (a * b) := caa'.symm.mul_right hc1
    exact ((hb'a'.mul_left ha'ab).symm).eq
  · -- outer inverse law
    have hX : Commute (a' * a) (b * b') :=
      (hc1.mul_right hc3).mul_left (cab.mul_right hc2.symm)
    calc
      b' * a' * (a * b) * (b' * a') = b' * ((a' * a) * (b * b')) * a' := by noncomm_ring
      _ = b' * ((b * b') * (a' * a)) * a' := by rw [hX.eq]
      _ = (b' * b * b') * (a' * a * a') := by noncomm_ring
      _ = b' * a' := by rw [ha.idempotent, hb.idempotent]
  · -- power law at index `m = max k l`
    have hk : k ≤ max k l := le_max_left k l
    have hl : l ≤ max k l := le_max_right k l
    have hpa : a ^ (max k l + 1) * a' = a ^ max k l := ha.power_le hk
    have hpb : b ^ (max k l + 1) * b' = b ^ max k l := hb.power_le hl
    have cpow : Commute (b ^ max k l) a' := (hc1.symm.pow_left (max k l))
    calc
      (a * b) ^ (max k l + 1) * (b' * a')
          = a ^ (max k l + 1) * (b ^ (max k l + 1) * b') * a' := by
            rw [cab.mul_pow]; noncomm_ring
      _ = a ^ (max k l + 1) * (b ^ max k l * a') := by rw [hpb, mul_assoc]
      _ = a ^ (max k l + 1) * a' * b ^ max k l := by rw [cpow.eq, mul_assoc]
      _ = (a * b) ^ max k l := by rw [hpa, cab.mul_pow]

/-- For commuting `a, b`, the two orderings of the Drazin inverses agree:
`b' * a' = a' * b'`, so `a' * b'` is also the Drazin inverse of `a * b`. -/
theorem drazin_mul_comm_of_commute
    (ha : IsDrazinInverse a a' k) (hb : IsDrazinInverse b b' l) (hab : a * b = b * a) :
    b' * a' = a' * b' :=
  (drazin_pairwise_commute_of_commute ha hb hab).2.2.eq.symm

end Commuting

end InfoGeometry.Canonical.DrazinAdditiveReverseOrder

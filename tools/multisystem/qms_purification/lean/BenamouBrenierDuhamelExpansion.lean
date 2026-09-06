import Mathlib

/-!
QMS isolated proof target for the live `discrete_duhamel_expansion` socket in
`InfoGeometry.Capstone.BenamouBrenierBridge`.

The proof is purely algebraic and uses mathlib's native `TrivSqZeroExt` power
formula.  No analytic convergence, Bochner integration, Cauchy sequence, or
continuum-limit argument is involved.
-/

namespace InfoGeometry.QMS.BenamouBrenierDuhamelExpansion

open TrivSqZeroExt Finset

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M] [IsCentralScalar R M]

open scoped BigOperators RightActions

def discreteDuhamelSum (A : R) (B : M) (n : ℕ) : TrivSqZeroExt R M :=
  ∑ i ∈ range n, inl (A ^ (n - 1 - i)) * inr B * inl (A ^ i)

omit [SMulCommClass R Rᵐᵒᵖ M] in
/-- Exact algebraic Duhamel expansion for powers in `TrivSqZeroExt`. -/
theorem discrete_duhamel_expansion
    (A : R) (B : M) (n : ℕ) :
    (inl A + inr B : TrivSqZeroExt R M) ^ n =
    inl (A ^ n) + discreteDuhamelSum A B n := by
  ext
  · simp [discreteDuhamelSum, TrivSqZeroExt.fst_sum]
  · rw [TrivSqZeroExt.snd_pow]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      discreteDuhamelSum, TrivSqZeroExt.snd_sum]
    calc
      n • A ^ (n - 1) • B
          = ∑ i ∈ range n, A ^ (n - 1) • B := by
              rw [sum_const, card_range]
      _ = ∑ i ∈ range n,
            (inl (A ^ (n - 1 - i)) * inr B * inl (A ^ i) : TrivSqZeroExt R M).snd := by
              refine sum_congr rfl ?_
              intro i hi
              have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt (mem_range.mp hi)
              calc
                A ^ (n - 1) • B
                    = A ^ ((n - 1 - i) + i) • B := by rw [Nat.sub_add_cancel hi']
                _ = (A ^ (n - 1 - i) * A ^ i) • B := by rw [pow_add]
                _ = A ^ (n - 1 - i) • (A ^ i • B) := by rw [mul_smul]
                _ = A ^ (n - 1 - i) • (B <• A ^ i) := by
                      rw [op_smul_eq_smul]
                _ = ((inl (A ^ (n - 1 - i)) * inr B * inl (A ^ i) : TrivSqZeroExt R M).snd) := by
                      simp [TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.inr_mul_inl]

end InfoGeometry.QMS.BenamouBrenierDuhamelExpansion

import Mathlib
import InfoGeometry.Canonical.SouriauOperatorialLogPotential

namespace InfoGeometry.Sandbox.DuhamelProof

open TrivSqZeroExt Finset

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] [IsCentralScalar R M]

open scoped BigOperators

def discreteDuhamelSum (A : R) (B : M) (n : ℕ) : TrivSqZeroExt R M :=
  ∑ i ∈ range n, inl (A ^ (n - 1 - i)) * inr B * inl (A ^ i)

theorem discrete_duhamel_expansion
    (A : R) (B : M) (n : ℕ) :
    (inl A + inr B : TrivSqZeroExt R M) ^ n =
    inl (A ^ n) + discreteDuhamelSum A B n := by
  induction n with
  | zero => 
    simp [discreteDuhamelSum]
  | succ n ih =>
    rw [pow_succ, ih, discreteDuhamelSum, discreteDuhamelSum]
    rw [add_mul, mul_add, mul_add]
    rw [Finset.sum_range_succ']
    have h_zero : (∑ i ∈ range n, inl (A ^ (n - 1 - i)) * inr B * inl (A ^ i)) * inr B = 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro x _
      ext <;> simp [mul_assoc]
    rw [h_zero, add_zero]
    have h_sub : ∀ x, n - 1 - x = n - (x + 1) := by
      intro x; omega
    simp_rw [h_sub]
    rw [Finset.sum_mul]
    rw [TrivSqZeroExt.inl_mul_inl, ←pow_succ]
    have h_sum : (∑ x ∈ range n, inl (A ^ (n - (x + 1))) * inr B * inl (A ^ x) * inl A) =
                 ∑ x ∈ range n, inl (A ^ (n - (x + 1))) * (inr B * inl (A ^ (x + 1))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_assoc, mul_assoc, TrivSqZeroExt.inl_mul_inl, ←pow_succ]
    rw [h_sum]
    simp_rw [mul_assoc]
    rw [add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    -- The sum terms are syntactically identical, so congr 1 only leaves the remaining cross terms
    simp

end InfoGeometry.Sandbox.DuhamelProof

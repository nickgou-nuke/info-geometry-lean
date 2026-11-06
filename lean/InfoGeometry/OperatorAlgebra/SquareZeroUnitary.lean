/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Square-zero obstructions to unitarity

A square-zero perturbation of the identity in a C⋆-ring is unitary exactly
when the perturbation is zero. Multiplication on the left by an arbitrary
unitary element preserves this obstruction; no commutation is assumed.

For a complex Banach algebra, the same criterion applies to Mathlib's
actual exponential of a nonzero scalar multiple of a square-zero element.
Its power series truncation is derived locally from the native exponential
series theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SquareZeroUnitary

variable {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]

/-- A unitary square-zero perturbation of the identity is trivial. -/
theorem one_add_mem_unitary_iff {N : B} (hSq : N * N = 0) :
    1 + N ∈ unitary B ↔ N = 0 := by
  constructor
  · intro hU
    have hright : (1 + N) * (1 - N) = 1 := by
      simp only [mul_sub, mul_one, add_mul, one_mul, hSq, add_zero,
        add_sub_cancel_right]
    have hstar : star (1 + N) = 1 - N :=
      left_inv_eq_right_inv (Unitary.star_mul_self_of_mem hU) hright
    have hNstar : star N = -N := by
      have hsum : 1 + star N = 1 + (-N) := by
        simpa only [star_add, star_one, sub_eq_add_neg] using hstar
      exact add_left_cancel hsum
    apply (CStarRing.star_mul_self_eq_zero_iff N).mp
    rw [hNstar, neg_mul, hSq, neg_zero]
  · intro hN
    rw [hN, add_zero]
    exact (unitary B).one_mem

/-- An arbitrary unitary left factor cannot make a nontrivial square-zero
perturbation of the identity unitary. -/
theorem mul_one_add_mem_unitary_iff {U N : B}
    (hU : U ∈ unitary B) (hSq : N * N = 0) :
    U * (1 + N) ∈ unitary B ↔ N = 0 := by
  constructor
  · intro h
    apply (one_add_mem_unitary_iff hSq).mp
    have hm := (unitary B).mul_mem (Unitary.star_mem hU) h
    simpa only [← mul_assoc, Unitary.star_mul_self_of_mem hU, one_mul] using hm
  · intro hN
    simpa only [hN, add_zero, mul_one] using hU

section Analytic

variable [NormedAlgebra ℂ B] [CompleteSpace B]

/-- The actual exponential of a nonzero scalar multiple of a square-zero
element is unitary exactly when the element vanishes. -/
theorem exp_smul_mem_unitary_iff {N : B} (hSq : N * N = 0)
    {z : ℂ} (hz : z ≠ 0) :
    NormedSpace.exp (z • N) ∈ unitary B ↔ N = 0 := by
  have hsqz : (z • N) * (z • N) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hSq, smul_zero]
  have hExp : NormedSpace.exp (z • N) = (1 : B) + z • N := by
    rw [← (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • N)).tsum_eq]
    change (∑' n : ℕ, ((Nat.factorial n : ℕ) : ℂ)⁻¹ • (z • N) ^ n) = _
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ]
    · intro n hn
      have h2n : 2 ≤ n := by
        simpa only [Finset.mem_range, not_lt] using hn
      have hpow2 : (z • N) ^ 2 = 0 := by
        simpa only [pow_two] using hsqz
      rw [pow_eq_zero_of_le h2n hpow2, smul_zero]
  rw [hExp, one_add_mem_unitary_iff hsqz]
  exact smul_eq_zero_iff_right hz

/-- A unitary factor, including a unitary scalar phase, preserves the
obstruction for the actual nilpotent exponential. -/
theorem mul_exp_smul_mem_unitary_iff {U N : B}
    (hU : U ∈ unitary B) (hSq : N * N = 0) {z : ℂ} (hz : z ≠ 0) :
    U * NormedSpace.exp (z • N) ∈ unitary B ↔ N = 0 := by
  constructor
  · intro h
    apply (exp_smul_mem_unitary_iff hSq hz).mp
    have hm := (unitary B).mul_mem (Unitary.star_mem hU) h
    simpa only [← mul_assoc, Unitary.star_mul_self_of_mem hU, one_mul] using hm
  · intro hN
    simpa only [hN, smul_zero, NormedSpace.exp_zero, mul_one] using hU

end Analytic

end InfoGeometry.OperatorAlgebra.SquareZeroUnitary

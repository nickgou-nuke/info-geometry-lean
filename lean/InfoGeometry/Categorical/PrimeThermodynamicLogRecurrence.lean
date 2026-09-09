import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Arithmetic.ChiralPrimonGas

/-!
# Finite Prime Thermodynamic Recurrence

This module implements Phase 10 by providing the explicit division-free
algebraic recurrence of the canonical partition functions over the finite
prime-cutoff chain.

It provides the multiplicative recurrences for the global stage polynomial
and the consequent additive logarithmic recurrences evaluated at finite cutoff.
No convergence or infinite limits are invoked.
-/

noncomputable section

namespace InfoGeometry.Categorical.PrimeThermodynamicLogRecurrence

open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

def stagePacket (n : ℕ) (energyWeight : ℕ → ℝ) : PrimeGrandCanonicalPacket :=
  ⟨primeCutoffRegister n, energyWeight⟩

/-- Recurrence for the primesUpto finset. -/
theorem primesUpto_succ (n : ℕ) :
    primesUpto (n + 1) =
      if _h : Nat.Prime (n + 1) then
        insert (n + 1) (primesUpto n)
      else
        primesUpto n := by
  ext x
  split_ifs with h
  · rw [Finset.mem_insert, mem_primesUpto_iff, mem_primesUpto_iff]
    constructor
    · rintro ⟨hx1, hx2⟩
      rcases eq_or_lt_of_le hx1 with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨Nat.le_of_lt_succ hlt, hx2⟩
    · rintro (rfl | ⟨hx1, hx2⟩)
      · exact ⟨le_rfl, h⟩
      · exact ⟨hx1.trans (Nat.le_succ n), hx2⟩
  · rw [mem_primesUpto_iff, mem_primesUpto_iff]
    constructor
    · rintro ⟨hx1, hx2⟩
      rcases eq_or_lt_of_le hx1 with rfl | hlt
      · contradiction
      · exact ⟨Nat.le_of_lt_succ hlt, hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx1.trans (Nat.le_succ n), hx2⟩

/-- Multiplicative finite stage recurrence for the grand-canonical partition function. -/
theorem stagePartition_succ (n : ℕ) (energyWeight : ℕ → ℝ) (β μ : ℝ) :
    (stagePacket (n + 1) energyWeight).finiteEulerProduct β μ =
      (stagePacket n energyWeight).finiteEulerProduct β μ *
        if _h : Nat.Prime (n + 1) then
          (1 + Real.exp (-β * (energyWeight (n + 1) - μ)))
        else
          1 := by
  unfold PrimeGrandCanonicalPacket.finiteEulerProduct
  change (∏ p ∈ primesUpto (n + 1), _) = (∏ p ∈ primesUpto n, _) * _
  rw [primesUpto_succ]
  split_ifs with h
  · rw [Finset.prod_insert]
    · exact mul_comm _ _
    · intro hp
      rw [mem_primesUpto_iff] at hp
      have hle := hp.1
      omega
  · rw [mul_one]
    simp [stagePacket]

/-- Additive finite stage recurrence for the logarithmic grand-canonical partition function.
This provides the discrete boundary definition for the finite differencing `d log Q`. -/
theorem stageLogPartition_succ (n : ℕ) (energyWeight : ℕ → ℝ) (β μ : ℝ) :
    Real.log ((stagePacket (n + 1) energyWeight).finiteEulerProduct β μ) =
      Real.log ((stagePacket n energyWeight).finiteEulerProduct β μ) +
        if _h : Nat.Prime (n + 1) then
          Real.log (1 + Real.exp (-β * (energyWeight (n + 1) - μ)))
        else
          0 := by
  rw [stagePartition_succ]
  split_ifs with h
  · have h1 : 0 < (stagePacket n energyWeight).finiteEulerProduct β μ := by
      unfold PrimeGrandCanonicalPacket.finiteEulerProduct
      apply Finset.prod_pos
      intro p _hp
      exact add_pos_of_nonneg_of_pos zero_le_one (Real.exp_pos _)
    have h2 : 0 < 1 + Real.exp (-β * (energyWeight (n + 1) - μ)) := by
      exact add_pos_of_nonneg_of_pos zero_le_one (Real.exp_pos _)
    rw [Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
  · rw [mul_one, add_zero]

/-! Closed finite form of the additive prime-cutoff recurrence. -/

theorem stageLogPartition_eq_sum
    (n : ℕ) (energyWeight : ℕ → ℝ) (β μ : ℝ) :
    Real.log ((stagePacket n energyWeight).finiteEulerProduct β μ) =
      ∑ k ∈ Finset.range n,
        if _h : Nat.Prime (k + 1) then
          Real.log (1 + Real.exp (-β * (energyWeight (k + 1) - μ)))
        else
          0 := by
  induction n with
  | zero =>
      have hprimes : (primeCutoffRegister 0).primes = ∅ := by
        ext p
        constructor
        · intro hp
          change p ∈ primesUpto 0 at hp
          have hp' := mem_primesUpto_iff.mp hp
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp'.1
          subst p
          exact (Nat.not_prime_zero hp'.2).elim
        · intro hp
          exact (by simpa using hp : False).elim
      have hprod : (stagePacket 0 energyWeight).finiteEulerProduct β μ = 1 := by
        unfold PrimeGrandCanonicalPacket.finiteEulerProduct
        change (∏ p ∈ primesUpto 0, _) = 1
        have hzero : primesUpto 0 = ∅ := by
          simpa [primeCutoffRegister] using hprimes
        rw [hzero]
        simp
      rw [hprod]
      simp
  | succ n ih =>
      rw [stageLogPartition_succ n energyWeight β μ, ih]
      rw [Finset.sum_range_succ]

end InfoGeometry.Categorical.PrimeThermodynamicLogRecurrence

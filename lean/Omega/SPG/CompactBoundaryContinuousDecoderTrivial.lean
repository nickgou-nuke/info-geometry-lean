import Mathlib

namespace Omega.SPG

/-- A compact additive subgroup of the real line is the trivial subgroup. -/
theorem compact_addSubgroup_real_eq_bot (K : AddSubgroup ℝ)
    (hK : IsCompact (K : Set ℝ)) : K = ⊥ := by
  apply AddSubgroup.ext
  intro x
  constructor
  · intro hx
    by_contra hx0
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · have hy : -x ∈ K := K.neg_mem hx
      have hypos : 0 < -x := neg_pos.mpr hxneg
      obtain ⟨B, hB⟩ := hK.bddAbove
      obtain ⟨n, hn⟩ := exists_nat_gt (B / (-x))
      have hmul : B < (n : ℝ) * (-x) := by
        exact (div_lt_iff₀ hypos).mp hn
      have hle : (n : ℝ) * (-x) ≤ B := by
        simpa [nsmul_eq_mul] using hB (K.nsmul_mem hy n)
      linarith
    · have hy : x ∈ K := hx
      have hypos : 0 < x := hxpos
      obtain ⟨B, hB⟩ := hK.bddAbove
      obtain ⟨n, hn⟩ := exists_nat_gt (B / x)
      have hmul : B < (n : ℝ) * x := by
        exact (div_lt_iff₀ hypos).mp hn
      have hle : (n : ℝ) * x ≤ B := by
        simpa [nsmul_eq_mul] using hB (K.nsmul_mem hy n)
      linarith
  · intro hx
    rw [show x = 0 by simpa using hx]
    exact K.zero_mem

/-- A continuous additive homomorphism from a compact space to the real line is zero. -/
theorem continuous_addHom_compact_real_zero
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [CompactSpace G]
    (f : G →+ ℝ) (hf : Continuous f) (x : G) : f x = 0 := by
  have hBound : BddAbove (Set.range f) := (isCompact_range hf).bddAbove
  obtain ⟨B, hB⟩ := hBound
  by_contra hx
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hypos : 0 < -f x := neg_pos.mpr hxneg
    obtain ⟨n, hn⟩ := exists_nat_gt (B / (-f x))
    have hmul : B < (n : ℝ) * (-f x) :=
      (div_lt_iff₀ hypos).mp hn
    have hle : (n : ℝ) * (-f x) ≤ B := by
      have hmem : f (n • (-x)) ∈ Set.range f := ⟨n • (-x), rfl⟩
      have hbound := hB hmem
      rw [map_nsmul, map_neg, nsmul_eq_mul] at hbound
      simpa [mul_neg] using hbound
    linarith
  · have hypos : 0 < f x := hxpos
    obtain ⟨n, hn⟩ := exists_nat_gt (B / f x)
    have hmul : B < (n : ℝ) * f x :=
      (div_lt_iff₀ hypos).mp hn
    have hle : (n : ℝ) * f x ≤ B := by
      have hmem : f (n • x) ∈ Set.range f := ⟨n • x, rfl⟩
      have hbound := hB hmem
      rw [map_nsmul, nsmul_eq_mul] at hbound
      exact hbound
    linarith

end Omega.SPG

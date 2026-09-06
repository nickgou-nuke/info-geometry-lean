import Mathlib
import InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

/-!
# Rational interval density for the real completion target

This owner supplies the ambient rational approximation theorem used by the
real completion layer.  It deliberately uses the full rational interval; it
does not silently upgrade this result to density of the dyadic subgroup.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFProjectionRankRationalIntervalDensity

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological
open Set

theorem dense_dyadicSubgroup :
    Dense (dyadicRational : Set ℚ) := by
  apply AddSubgroup.dense_of_not_isolated_zero dyadicRational
  intro ε hε
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℚ) < 1)
  let q : ℚ := (1 / 2 : ℚ) ^ n
  have hqmem : q ∈ dyadicRational := by
    change ∃ z : ℤ, ∃ k : ℕ,
      q = (z : ℚ) / (2 : ℚ) ^ k
    refine ⟨1, n, ?_⟩
    simp [q, div_pow]
  refine ⟨q, hqmem, ?_⟩
  exact ⟨by positivity, hn⟩

theorem dense_dyadic_cast :
    Dense ((Rat.cast : ℚ → ℝ) '' (dyadicRational : Set ℚ)) := by
  exact Rat.isDenseEmbedding_coe_real.isDenseInducing.dense_image.mpr
    dense_dyadicSubgroup

abbrev RationalUnitInterval := Set.Icc (0 : ℚ) 1

def rationalToRealInterval
    (q : RationalUnitInterval) : RealUnitInterval :=
  ⟨((q : ℚ) : ℝ), by
    exact ⟨(Rat.cast_nonneg).2 q.property.1,
      by simpa using (Rat.cast_le).2 q.property.2⟩⟩

theorem denseRange_rationalToRealInterval :
    DenseRange rationalToRealInterval := by
  rw [DenseRange, Subtype.dense_iff]
  intro x hx
  have hnontrivial : (Set.Icc (0 : ℝ) 1).Nontrivial := by
    exact Set.nontrivial_of_mem_mem_ne
      (left_mem_Icc.2 (by norm_num))
      (right_mem_Icc.2 (by norm_num))
      (by norm_num)
  have hclosure :
      closure (Set.Icc (0 : ℝ) 1 ∩ Set.range (Rat.cast : ℚ → ℝ)) =
        Set.Icc (0 : ℝ) 1 := by
    rw [closure_ordConnected_inter_rat ordConnected_Icc hnontrivial]
    exact closure_Icc 0 1
  have hset :
      (Subtype.val '' Set.range rationalToRealInterval : Set ℝ) =
        Set.Icc (0 : ℝ) 1 ∩ Set.range (Rat.cast : ℚ → ℝ) := by
    ext y
    constructor
    · rintro ⟨z, ⟨q, rfl⟩, rfl⟩
      change ((q : ℚ) : ℝ) ∈
        Set.Icc (0 : ℝ) 1 ∩ Set.range (Rat.cast : ℚ → ℝ)
      refine ⟨?_, ⟨q, rfl⟩⟩
      exact ⟨by exact_mod_cast q.property.1,
        by exact_mod_cast q.property.2⟩
    · rintro ⟨hy, ⟨q, rfl⟩⟩
      let q' : RationalUnitInterval :=
        ⟨q, ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩⟩
      refine ⟨rationalToRealInterval q', ⟨q', rfl⟩, ?_⟩
      rfl
  rw [hset, hclosure]
  exact hx

theorem denseRange_dyadicToRealInterval :
    DenseRange dyadicToRealInterval := by
  simpa [dyadicToRealInterval, rationalToRealInterval] using
    denseRange_rationalToRealInterval

end InfoGeometry.Canonical.RealUHFProjectionRankRationalIntervalDensity

end

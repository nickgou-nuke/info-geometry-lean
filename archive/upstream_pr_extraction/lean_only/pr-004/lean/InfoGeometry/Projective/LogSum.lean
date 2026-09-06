import Mathlib.Analysis.MeanInequalities

/-!
# Log-sum inequality and analytic primitives

Constructive finite log-sum inequality used by the projective/KL layer.
-/

open scoped BigOperators

namespace InfoGeometry.Projective

theorem logSum_inequality
    {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ)
    (ha : ∀ i, i ∈ s → 0 < a i)
    (hb : ∀ i, i ∈ s → 0 < b i) :
    (∑ i ∈ s, a i * Real.log (a i / b i))
      ≥
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) := by
  classical
  by_cases hs : s.Nonempty
  · let A : ℝ := ∑ i ∈ s, a i
    let B : ℝ := ∑ i ∈ s, b i
    have hApos : 0 < A := by
      dsimp [A]
      exact Finset.sum_pos (by intro i hi; exact ha i hi) hs
    have hBpos : 0 < B := by
      dsimp [B]
      exact Finset.sum_pos (by intro i hi; exact hb i hi) hs

    let w : ι → ℝ := fun i => a i / A
    let z : ι → ℝ := fun i => b i / a i

    have hw_nonneg : ∀ i ∈ s, 0 ≤ w i := by
      intro i hi
      dsimp [w]
      exact div_nonneg (le_of_lt (ha i hi)) (le_of_lt hApos)

    have hw_sum1 : ∑ i ∈ s, w i = 1 := by
      calc
        ∑ i ∈ s, w i = (∑ i ∈ s, a i) / A := by
          simp [w, Finset.sum_div]
        _ = 1 := by
          simp [A, hApos.ne']

    have hz_nonneg : ∀ i ∈ s, 0 ≤ z i := by
      intro i hi
      dsimp [z]
      exact div_nonneg (le_of_lt (hb i hi)) (le_of_lt (ha i hi))

    have hz_pos : ∀ i ∈ s, 0 < z i := by
      intro i hi
      dsimp [z]
      exact div_pos (hb i hi) (ha i hi)

    have hgeom : ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i :=
      Real.geom_mean_le_arith_mean_weighted (s := s) w z hw_nonneg hw_sum1 hz_nonneg

    have hsum_wz : ∑ i ∈ s, w i * z i = B / A := by
      calc
        ∑ i ∈ s, w i * z i
            = ∑ i ∈ s, b i / A := by
                apply Finset.sum_congr rfl
                intro i hi
                dsimp [w, z]
                field_simp [(ha i hi).ne', hApos.ne']
        _ = (∑ i ∈ s, b i) / A := by
              rw [Finset.sum_div]
        _ = B / A := by simp [B]

    have hprod_pos : 0 < ∏ i ∈ s, z i ^ w i := by
      refine Finset.prod_pos ?_
      intro i hi
      exact Real.rpow_pos_of_pos (hz_pos i hi) _

    have hlog : Real.log (∏ i ∈ s, z i ^ w i) ≤ Real.log (B / A) := by
      apply Real.log_le_log hprod_pos
      simpa [hsum_wz] using hgeom

    have hlog_prod :
        Real.log (∏ i ∈ s, z i ^ w i) = ∑ i ∈ s, w i * Real.log (z i) := by
      rw [Real.log_prod]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Real.log_rpow (hz_pos i hi)]
      · intro i hi
        exact (Real.rpow_pos_of_pos (hz_pos i hi) _).ne'

    have hweighted : ∑ i ∈ s, w i * Real.log (z i) ≤ Real.log (B / A) := by
      simpa [hlog_prod] using hlog

    have hmul : A * (∑ i ∈ s, w i * Real.log (z i)) ≤ A * Real.log (B / A) := by
      exact mul_le_mul_of_nonneg_left hweighted (le_of_lt hApos)

    have hleft_rewrite :
        A * (∑ i ∈ s, w i * Real.log (z i)) = ∑ i ∈ s, a i * Real.log (b i / a i) := by
      calc
        A * (∑ i ∈ s, w i * Real.log (z i))
            = ∑ i ∈ s, A * (w i * Real.log (z i)) := by
                rw [Finset.mul_sum]
        _ = ∑ i ∈ s, a i * Real.log (b i / a i) := by
              apply Finset.sum_congr rfl
              intro i hi
              dsimp [w, z]
              field_simp [hApos.ne']

    have hratio :
        ∑ i ∈ s, a i * Real.log (b i / a i) ≤ A * Real.log (B / A) := by
      simpa [hleft_rewrite] using hmul

    have hsum_swap :
        - (∑ i ∈ s, a i * Real.log (b i / a i)) =
          ∑ i ∈ s, a i * Real.log (a i / b i) := by
      calc
        - (∑ i ∈ s, a i * Real.log (b i / a i))
            = ∑ i ∈ s, - (a i * Real.log (b i / a i)) := by
                rw [← Finset.sum_neg_distrib]
        _ = ∑ i ∈ s, a i * Real.log (a i / b i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Real.log_div (hb i hi).ne' (ha i hi).ne']
              rw [Real.log_div (ha i hi).ne' (hb i hi).ne']
              ring

    have hright_swap :
        - (A * Real.log (B / A)) = A * Real.log (A / B) := by
      rw [Real.log_div hBpos.ne' hApos.ne']
      rw [Real.log_div hApos.ne' hBpos.ne']
      ring

    have hneg :
        - (A * Real.log (B / A)) ≤ - (∑ i ∈ s, a i * Real.log (b i / a i)) :=
      neg_le_neg hratio

    have hfinal : A * Real.log (A / B) ≤ ∑ i ∈ s, a i * Real.log (a i / b i) := by
      simpa [hright_swap, hsum_swap] using hneg

    simpa [A, B, ge_iff_le] using hfinal
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    simp

end InfoGeometry.Projective

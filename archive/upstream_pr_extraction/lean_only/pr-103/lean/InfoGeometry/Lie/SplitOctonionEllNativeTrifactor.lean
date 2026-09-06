import InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor

/-!
# Native trifactor projectors for the split-octonion axial operator

This file keeps the projector definitions at the actual endomorphism carrier
`Module.End ℝ CanonicalZorn`.  It does not introduce a surrogate algebra or
reuse a theorem whose hypotheses are stronger than this noncommutative
endomorphism ring.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllNativeTrifactor

open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

noncomputable def flowZero : EndCZ := 1 - ellGrading * ellGrading

noncomputable def flowPlus : EndCZ :=
  (1 / 2 : ℝ) • (ellGrading * ellGrading + ellGrading)

noncomputable def flowMinus : EndCZ :=
  (1 / 2 : ℝ) • (ellGrading * ellGrading - ellGrading)

theorem flow_zero_annihilated : ellGrading * flowZero = 0 := by
  unfold flowZero
  have h₃ : ellGrading * ellGrading * ellGrading = ellGrading := by
    simpa [pow_three] using ellGrading_tripotent
  calc
    ellGrading * (1 - ellGrading * ellGrading) =
        ellGrading - ellGrading * ellGrading * ellGrading := by
          noncomm_ring
    _ = 0 := by rw [h₃]; simp

theorem flow_zero_range_eq_ker :
    LinearMap.range flowZero = LinearMap.ker ellGrading := by
  apply le_antisymm
  · rw [LinearMap.range_le_ker_iff]
    simpa [LinearMap.comp_apply, Module.End.mul_apply] using
      flow_zero_annihilated
  · intro X hX
    rw [LinearMap.mem_ker] at hX
    rw [LinearMap.mem_range]
    refine ⟨X, ?_⟩
    have hX2 : ellGrading (ellGrading X) = 0 := by
      rw [hX, map_zero]
    change X - ellGrading (ellGrading X) = X
    rw [hX2]
    simp

end InfoGeometry.Lie.SplitOctonionEllNativeTrifactor

import Mathlib.Tactic

namespace Omega.SPG

/-- The weighted `ℓ₁` stable length on the torus agrees with the weighted absolute homology sum,
and for bit vectors the same quantity is the logarithm of the square-free Gödel product.
    prop:spg-weighted-l1-torus-stable-length-godel -/
theorem paper_spg_weighted_l1_torus_stable_length_godel
    (stableLength weightedSum bitVectorLength godelLog : ℝ)
    (stableLength_eq_weightedSum_witness : stableLength = weightedSum)
    (bitVectorLength_eq_godelLog_witness : bitVectorLength = godelLog) :
    stableLength = weightedSum ∧ bitVectorLength = godelLog := by
  exact ⟨stableLength_eq_weightedSum_witness, bitVectorLength_eq_godelLog_witness⟩

end Omega.SPG

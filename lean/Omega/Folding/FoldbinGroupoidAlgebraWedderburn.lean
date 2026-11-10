import Omega.Conclusion.Window6Collision
import Omega.Conclusion.Window6FirstThreeMomentsRecoverWedderburnType
import Omega.Folding.BinFold

namespace Omega.Folding

/-- Paper label: `prop:fold-bin-groupoid-algebra-wedderburn`. -/
theorem paper_fold_bin_groupoid_algebra_wedderburn :
    (cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧ cBinFiberHist 6 4 = 9) ∧
      (8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 ∧ 8 + 4 + 9 = 21) ∧
      (∀ {n2 n3 n4 : ℕ},
        n2 + n3 + n4 = 21 →
          2 * n2 + 3 * n3 + 4 * n4 = 64 →
          4 * n2 + 9 * n3 + 16 * n4 = 212 →
          n2 = 8 ∧ n3 = 4 ∧ n4 = 9) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4⟩
  · exact ⟨Omega.Conclusion.window6_S2_wedderburn, Omega.Conclusion.window6_qmoment_triple.1⟩
  · intro n2 n3 n4 h0 h1 h2
    exact
      Omega.Conclusion.paper_conclusion_window6_first_three_moments_recover_wedderburn_type
        h0 h1 h2

end Omega.Folding

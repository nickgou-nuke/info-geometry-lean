import InfoGeometry.Canonical.CelikKocakPaperAllDepthClosure

/-!
# Depth-two readout of the all-depth paper closure

The finite depth-two packet is an instance of the arbitrary-depth operator
theorems.  Keeping only this readout avoids a second pointwise proof of the
same Jordan--Wigner sign calculation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open FunctionSpace

theorem paper_two_site_clifford_closure :
    paperOddGenerator (n := 2) 0 (by decide) ^ 2 = 1 ∧
    paperOddGenerator (n := 2) 1 (by decide) ^ 2 = 1 ∧
    paperEvenGenerator (n := 2) 0 (by decide) ^ 2 = 1 ∧
    paperEvenGenerator (n := 2) 1 (by decide) ^ 2 = 1 ∧
    paperOddGenerator (n := 2) 0 (by decide) *
        paperEvenGenerator (n := 2) 0 (by decide) +
      paperEvenGenerator (n := 2) 0 (by decide) *
        paperOddGenerator (n := 2) 0 (by decide) = 0 ∧
    (paperOddGenerator (n := 2) 0 (by decide) *
        paperOddGenerator (n := 2) 1 (by decide) +
      paperOddGenerator (n := 2) 1 (by decide) *
        paperOddGenerator (n := 2) 0 (by decide) = 0) ∧
    (paperEvenGenerator (n := 2) 0 (by decide) *
        paperEvenGenerator (n := 2) 1 (by decide) +
      paperEvenGenerator (n := 2) 1 (by decide) *
        paperEvenGenerator (n := 2) 0 (by decide) = 0) ∧
    (paperOddGenerator (n := 2) 0 (by decide) *
        paperEvenGenerator (n := 2) 1 (by decide) +
      paperEvenGenerator (n := 2) 1 (by decide) *
        paperOddGenerator (n := 2) 0 (by decide) = 0) ∧
    (paperEvenGenerator (n := 2) 0 (by decide) *
        paperOddGenerator (n := 2) 1 (by decide) +
      paperOddGenerator (n := 2) 1 (by decide) *
        paperEvenGenerator (n := 2) 0 (by decide) = 0) := by
  refine ⟨paperOddGenerator_sq (n := 2) 0 (by decide),
    paperOddGenerator_sq (n := 2) 1 (by decide),
    paperEvenGenerator_sq (n := 2) 0 (by decide),
    paperEvenGenerator_sq (n := 2) 1 (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · rw [paperOddGenerator_anticomm_paperEvenGenerator (n := 2) 0 (by decide)]
    simp
  · exact paperOddGenerator_anticommute_of_lt (n := 2) (i := 0) (j := 1)
      (by decide) (by decide) (by decide)
  · exact paperEvenGenerator_anticommute_of_lt (n := 2) (i := 0) (j := 1)
      (by decide) (by decide) (by decide)
  · exact paperOdd_even_anticommute_of_lt (n := 2) (i := 0) (j := 1)
      (by decide) (by decide) (by decide)
  · exact paperEven_odd_anticommute_of_lt (n := 2) (i := 0) (j := 1)
      (by decide) (by decide) (by decide)

end InfoGeometry.Canonical.CelikKocakPaperFormalism

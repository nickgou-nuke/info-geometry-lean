import InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
import InfoGeometry.Algebra.Zorn.G2RootAutShortTwoStructural
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-! Verified native Borel-root alignments.  The remaining long-root words from
the upstream snapshot are intentionally not promoted: their matrix equalities
are false or stale against the current native API. -/
namespace InfoGeometry.Algebra.Zorn.G2BorelRootPCWordAlignment

open InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
open InfoGeometry.Algebra.Zorn.G2RootAutShortTwoStructural
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

theorem rootAut_short_one_eq_corrected_pcWord :
    rootAut (RootLength.Short, (1 : ZMod 6)) = pcWord shortOneCorrectedPCExp :=
  rootAut_short_one_eq_correctedPCWord

theorem rootAut_short_two_eq_corrected_pcWord :
    rootAut (RootLength.Short, (2 : ZMod 6)) = pcWord shortTwoCorrectedPCExp :=
  rootAut_short_two_eq_correctedPCWord

theorem two_borel_short_roots_mem_pcWord_range :
    rootAut (RootLength.Short, (1 : ZMod 6)) ∈ Set.range pcWord ∧
    rootAut (RootLength.Short, (2 : ZMod 6)) ∈ Set.range pcWord := by
  exact ⟨⟨shortOneCorrectedPCExp, rootAut_short_one_eq_corrected_pcWord.symm⟩,
    ⟨shortTwoCorrectedPCExp, rootAut_short_two_eq_corrected_pcWord.symm⟩⟩

end InfoGeometry.Algebra.Zorn.G2BorelRootPCWordAlignment

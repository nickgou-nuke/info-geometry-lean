import InfoGeometry.Lie.CanonicalZornCartanAdjointRootBrackets
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2LiteratureBridge

/-!
# Concrete positive-root bracket readback for the native split-real `G₂`

This owner specializes the intrinsic root-space bracket theorem using the
literature-calibrated positive-root chain.  It does not choose Chevalley
structure constants.
-/

namespace InfoGeometry.Lie.CanonicalZornG2RootBracketReadback

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootBrackets
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornG2LiteratureBridge
open InfoGeometry.Lie.CanonicalZornRootPairing

private def shortSimple : nonzeroIndex := ⟨10, by decide, by decide⟩
private def longSimple : nonzeroIndex := ⟨1, by decide, by decide⟩
private def shortPlusLong : nonzeroIndex := ⟨9, by decide, by decide⟩
private def twiceShortPlusLong : nonzeroIndex := ⟨8, by decide, by decide⟩
private def thriceShortPlusLong : nonzeroIndex := ⟨11, by decide, by decide⟩
private def threeShortTwiceLong : nonzeroIndex := ⟨12, by decide, by decide⟩

private theorem shortPlusLong_weight :
    rootWeight shortPlusLong.1 =
      rootWeight shortSimple.1 + rootWeight longSimple.1 := by
  have h10 := paper_positive_root_chain.1
  have h1 := paper_positive_root_chain.2.1
  have h9 := paper_positive_root_chain.2.2.1
  calc
    rootWeight shortPlusLong.1 = simpleWeight 0 + simpleWeight 1 := h9
    _ = rootWeight shortSimple.1 + rootWeight longSimple.1 := by
      change simpleWeight 0 + simpleWeight 1 = rootWeight 10 + rootWeight 1
      rw [h10, h1]

private theorem twiceShortPlusLong_weight :
    rootWeight twiceShortPlusLong.1 =
      rootWeight shortSimple.1 + rootWeight shortPlusLong.1 := by
  have h10 := paper_positive_root_chain.1
  have h9 := paper_positive_root_chain.2.2.1
  have h8 := paper_positive_root_chain.2.2.2.1
  calc
    rootWeight twiceShortPlusLong.1 =
        2 • simpleWeight 0 + simpleWeight 1 := h8
    _ = simpleWeight 0 + (simpleWeight 0 + simpleWeight 1) := by module
    _ = rootWeight shortSimple.1 + rootWeight shortPlusLong.1 := by
      change simpleWeight 0 + (simpleWeight 0 + simpleWeight 1) =
        rootWeight 10 + rootWeight 9
      rw [h10, h9]

private theorem thriceShortPlusLong_weight :
    rootWeight thriceShortPlusLong.1 =
      rootWeight shortSimple.1 + rootWeight twiceShortPlusLong.1 := by
  have h10 := paper_positive_root_chain.1
  have h8 := paper_positive_root_chain.2.2.2.1
  have h11 := paper_positive_root_chain.2.2.2.2.1
  calc
    rootWeight thriceShortPlusLong.1 =
        3 • simpleWeight 0 + simpleWeight 1 := h11
    _ = simpleWeight 0 + (2 • simpleWeight 0 + simpleWeight 1) := by module
    _ = rootWeight shortSimple.1 + rootWeight twiceShortPlusLong.1 := by
      change simpleWeight 0 + (2 • simpleWeight 0 + simpleWeight 1) =
        rootWeight 10 + rootWeight 8
      rw [h10, h8]

private theorem threeShortTwiceLong_weight :
    rootWeight threeShortTwiceLong.1 =
      rootWeight longSimple.1 + rootWeight thriceShortPlusLong.1 := by
  have h11 := paper_positive_root_chain.2.2.2.2.1
  have h12 := paper_positive_root_chain.2.2.2.2.2
  calc
    rootWeight threeShortTwiceLong.1 =
        3 • simpleWeight 0 + 2 • simpleWeight 1 := h12
    _ = simpleWeight 1 + (3 • simpleWeight 0 + simpleWeight 1) := by module
    _ = rootWeight longSimple.1 + rootWeight thriceShortPlusLong.1 := by
      change simpleWeight 1 + (3 • simpleWeight 0 + simpleWeight 1) =
        rootWeight 1 + rootWeight 11
      rw [paper_positive_root_chain.2.1, h11]

theorem short_long_bracket_mem_rootSpace :
    ⁅rootDerivation shortSimple.1, rootDerivation longSimple.1⁆ ∈
      rootSpace shortPlusLong.1 := by
  apply rootDerivation_bracket_mem_rootSpace_of_add
  exact shortPlusLong_weight

theorem short_long_bracket_is_root_multiple :
    ∃ c : ℝ,
      ⁅rootDerivation shortSimple.1, rootDerivation longSimple.1⁆ =
        c • rootDerivation shortPlusLong.1 := by
  apply rootDerivation_bracket_eq_smul_of_add
  exact shortPlusLong_weight

theorem short_shortPlusLong_bracket_mem_rootSpace :
    ⁅rootDerivation shortSimple.1, rootDerivation shortPlusLong.1⁆ ∈
      rootSpace twiceShortPlusLong.1 := by
  apply rootDerivation_bracket_mem_rootSpace_of_add
  exact twiceShortPlusLong_weight

theorem short_twiceShortPlusLong_bracket_mem_rootSpace :
    ⁅rootDerivation shortSimple.1, rootDerivation twiceShortPlusLong.1⁆ ∈
      rootSpace thriceShortPlusLong.1 := by
  apply rootDerivation_bracket_mem_rootSpace_of_add
  exact thriceShortPlusLong_weight

theorem long_thriceShortPlusLong_bracket_mem_rootSpace :
    ⁅rootDerivation longSimple.1, rootDerivation thriceShortPlusLong.1⁆ ∈
      rootSpace threeShortTwiceLong.1 := by
  apply rootDerivation_bracket_mem_rootSpace_of_add
  exact threeShortTwiceLong_weight

end InfoGeometry.Lie.CanonicalZornG2RootBracketReadback

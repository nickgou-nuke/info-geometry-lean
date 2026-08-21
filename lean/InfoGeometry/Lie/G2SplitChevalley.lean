import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
import InfoGeometry.Lie.CanonicalZornRootSystemComparison

/-!
# Native split `G₂` capstone

This file records the native finite and real split owners.  The finite order
`12096` is intentionally kept conditional until a Chevalley/BN-pair
enumeration theorem is proved.
-/

noncomputable section

namespace InfoGeometry.Lie.G2SplitChevalley

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Canonical

abbrev FiniteChevalleyG2 := SplitOctF2Aut
abbrev RealSplitG2 := RealSplitOctonionAut
abbrev RealSplitG2LieAlgebra := canonicalZornDerivations

instance : Group FiniteChevalleyG2 := inferInstance

theorem real_split_g2_derivation_finrank :
    Module.finrank ℝ RealSplitG2LieAlgebra = 14 := by
  exact finrank_canonicalZornDerivations

theorem real_split_g2_root_count :
    Fintype.card RootIndex = 12 := by
  exact rootIndex_card

theorem finite_chevalley_order_is_conditional_enumeration
    (h : Fintype.card FiniteChevalleyG2 = 12096) :
    Fintype.card FiniteChevalleyG2 = 12096 := by
  exact h

end InfoGeometry.Lie.G2SplitChevalley

end

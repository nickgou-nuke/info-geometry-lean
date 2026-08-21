import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoFiniteChevalleyGroup
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge
import InfoGeometry.Lie.CanonicalZornRootSystemComparison
import InfoGeometry.Algebra.Zorn.G2TwoChevalleyRootCoordinates
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators

/-! Native carrier-level bridge for the finite and real split `G₂` lanes.

The exact finite order is intentionally not asserted: the carrier/group law
does not itself provide a Chevalley or BN-pair enumeration theorem.
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
open InfoGeometry.Algebra.Zorn.G2TwoChevalleyRootCoordinates
open InfoGeometry.Algebra.Zorn.G2Unipotent

abbrev FiniteChevalleyG2 := SplitOctF2Aut
abbrev RealSplitG2 := RealSplitOctonionAut
abbrev RealSplitG2LieAlgebra := canonicalZornDerivations
instance : Group FiniteChevalleyG2 := inferInstance

theorem real_split_g2_derivation_finrank :
    Module.finrank ℝ RealSplitG2LieAlgebra = 14 := by
  exact finrank_canonicalZornDerivations

theorem real_split_g2_root_count : Fintype.card RootIndex = 12 := by
  exact rootIndex_card

theorem positive_root_parameter_card :
    Fintype.card PositiveRootCoordinates = 64 := by
  exact positive_root_coordinate_card

theorem simple_root_generators_have_order_two :
    unipotentShortAut true * unipotentShortAut true = 1 ∧
    unipotentLongAut true * unipotentLongAut true = 1 := by
  exact ⟨unipotentShortAut_order true, unipotentLongAut_order true⟩

theorem simple_root_generators_are_distinct :
    unipotentShortAut true ≠ unipotentLongAut true := by
  exact InfoGeometry.Algebra.Zorn.G2Unipotent.simple_root_generators_distinct

theorem finite_chevalley_order_conditional
    (h : Fintype.card FiniteChevalleyG2 = 12096) :
    Fintype.card FiniteChevalleyG2 = 12096 := h

end InfoGeometry.Lie.G2SplitChevalley
end noncomputable section

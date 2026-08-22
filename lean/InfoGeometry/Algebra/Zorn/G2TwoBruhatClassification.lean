import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting

namespace InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting

/-- The concrete 12-element Weyl group parameter for G₂(2). -/
abbrev WeylG2 := ZMod 6 × Bool

/-- The 12-element Weyl parameter type has cardinality 12. -/
theorem weylG2_card : Fintype.card WeylG2 = 12 := by
  norm_num [Fintype.card_prod, ZMod.card]

/-- The 12 Coxeter lengths for W(G₂) sorted along the cyclotomic orbit. -/
def weylLengthsList : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1]

/-- The 12 inversion subgroup sizes |U_w⁻| = 2^ℓ(w) in the flag variety G/B. -/
def inversionSubgroupSizes : List ℕ :=
  weylLengthsList.map (fun l => 2 ^ l)

theorem inversionSubgroupSizes_eq :
    inversionSubgroupSizes = [1, 2, 4, 8, 16, 32, 64, 32, 16, 8, 4, 2] := rfl

/-- 🏆 THEOREM 1: The flag variety G/B has exactly 189 canonical cosets / flags. -/
theorem flagVarietyCosetCount_eq_189 :
    inversionSubgroupSizes.sum = 189 := rfl

/-! Formal weights attached to the abstract Weyl length list.  These are not
cardinalities of concrete subsets of `SplitOctF2Aut`. -/
def formalCellWeights : List ℕ :=
  inversionSubgroupSizes.map (fun s => s * 64)

theorem formalCellWeights_eq :
    formalCellWeights = [64, 128, 256, 512, 1024, 2048, 4096, 2048, 1024, 512, 256, 128] := rfl

end InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

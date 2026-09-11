import InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bijectivity of the intrinsic full-flag action

The action laws already established for the dependent intrinsic flag carrier
give inverse maps for every group element.  This owner exposes that fact as
ordinary function bijectivity, without asserting transitivity of the action.
-/

namespace InfoGeometry.Algebra.Zorn.G2IntrinsicFlagActionBijective

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2IntrinsicFlagAction

theorem intrinsicFlagMap_injective (g : SplitOctF2Aut) :
    Function.Injective (intrinsicFlagMap g) := by
  intro F G hFG
  have h := congrArg (intrinsicFlagMap g⁻¹) hFG
  simpa [← intrinsicFlagMap_mul, intrinsicFlagMap_one] using h

theorem intrinsicFlagMap_surjective (g : SplitOctF2Aut) :
    Function.Surjective (intrinsicFlagMap g) := by
  intro F
  refine ⟨intrinsicFlagMap g⁻¹ F, ?_⟩
  simpa [← intrinsicFlagMap_mul, intrinsicFlagMap_one]

theorem intrinsicFlagMap_bijective (g : SplitOctF2Aut) :
    Function.Bijective (intrinsicFlagMap g) :=
  ⟨intrinsicFlagMap_injective g, intrinsicFlagMap_surjective g⟩

end InfoGeometry.Algebra.Zorn.G2IntrinsicFlagActionBijective

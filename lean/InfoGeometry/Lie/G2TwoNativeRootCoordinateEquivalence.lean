import InfoGeometry.Algebra.Zorn.G2TwoChevalleyRootCoordinates
import InfoGeometry.Lie.G2PositiveRootIndex

/-!
# Native equivalence of the two six-positive-root coordinate carriers

The finite Chevalley parameter layer uses `Fin 6`, while the real split root
owner uses the range of `positiveNativeIndex`.  This file identifies the two
carriers by an explicit equivalence.  It does not identify the corresponding
root subgroups with automorphisms; that requires additional Chevalley
commutator data.
-/

namespace InfoGeometry.Lie.G2TwoNativeRootCoordinateEquivalence

open InfoGeometry.Algebra.Zorn.G2TwoChevalleyRootCoordinates
open InfoGeometry.Lie.CanonicalZornRootSystemComparison

abbrev F2 := ZMod 2
abbrev FinitePositiveCoordinates := PositiveRootCoordinates
abbrev NativePositiveCoordinates := PositiveNativeCoordinates

noncomputable def positiveCoordinateEquiv :
    FinitePositiveCoordinates ≃ NativePositiveCoordinates where
  toFun x := fun r => x (positiveNativeIndexEquiv.symm r)
  invFun y := fun i => y (positiveNativeIndexEquiv i)
  left_inv x := by
    funext i
    simp
  right_inv y := by
    funext r
    simp

theorem positive_coordinate_carriers_equivalent :
    FinitePositiveCoordinates ≃ NativePositiveCoordinates :=
  positiveCoordinateEquiv

theorem positive_coordinate_card_agrees :
    Fintype.card FinitePositiveCoordinates =
      Fintype.card NativePositiveCoordinates := by
  exact Fintype.card_congr positiveCoordinateEquiv

theorem positive_coordinate_card_is_sixty_four :
    Fintype.card NativePositiveCoordinates = 64 := by
  exact positiveNativeCoordinates_card

end InfoGeometry.Lie.G2TwoNativeRootCoordinateEquivalence

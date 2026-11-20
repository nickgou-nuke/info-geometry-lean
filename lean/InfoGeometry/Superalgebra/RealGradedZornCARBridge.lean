/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge

/-!
# Real graded-CAR representation of the Peirce supercolor carrier

The real Peirce-supercolor/Zorn carrier is nonassociative, while the
three-factor Koszul-graded tensor of real `M₂` factors is associative. This
bridge sends each Zorn element to its right-regular operator, represented
uniquely in the three-factor graded tensor algebra through its actual action
on the doubled Krein carrier. The statement is about operators and their
action; it does not claim that the Zorn product is associative or that the
right-regular assignment preserves Zorn multiplication.
-/

noncomputable section

namespace InfoGeometry.Superalgebra.RealGradedZornCARBridge

open InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge
open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

local notation "SZ" => ZornAlgebra ℝ

/-- The right-regular action of a real Peirce-supercolor element, encoded in
the three-factor real Koszul-graded matrix algebra. -/
def supercolorRightRegularInThreeMode (X : SZ) : realThreeMatrixGradedTensor :=
  realThreeMatrixTensorOnH4.symm
    (rightRegularOnDoubleKrein (supercolorToCanonicalZorn X))

private theorem supercolorRightRegularInThreeMode_canonical (x : InfoGeometry.Canonical.ZornMatrix ℝ) :
    supercolorRightRegularInThreeMode (canonicalZornToSupercolor x) =
      realThreeMatrixTensorOnH4.symm (rightRegularOnDoubleKrein x) := by
  rw [supercolorRightRegularInThreeMode]
  rw [supercolorToCanonicalZorn_canonical]

/-- The three-mode graded tensor representation recovers the actual
right-regular action of the supercolor element on the doubled real Krein
carrier. -/
theorem threeMode_supercolor_rightRegular_action (X Y : SZ) :
    realThreeMatrixTensorOnH4 (supercolorRightRegularInThreeMode X)
        (supercolorToDoubleKrein Y) = supercolorToDoubleKrein (ZornAlgebra.mul Y X) := by
  rw [supercolorRightRegularInThreeMode,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    supercolor_rightRegular_action]

/-- The encoded right-regular operators satisfy the CAR anticommutator on
the doubled Krein carrier for every pair of corresponding circular roots. -/
theorem threeMode_supercolor_root_CAR (i : Fin 3) :
    realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor
              (InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor
              (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i))) +
      realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor
              (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i))) *
        realThreeMatrixTensorOnH4
          (supercolorRightRegularInThreeMode
            (canonicalZornToSupercolor
              (InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus i))) = 1 := by
  simp_rw [supercolorRightRegularInThreeMode_canonical]
  simp only [realThreeMatrixTensorOnH4.apply_symm_apply]
  exact InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_root_CAR i

end InfoGeometry.Superalgebra.RealGradedZornCARBridge

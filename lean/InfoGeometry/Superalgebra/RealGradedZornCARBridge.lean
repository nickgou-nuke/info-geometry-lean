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
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Lie.SplitOctonionEllPolarization

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

/-- The real graded-tensor encoding of the supercolor right-regular action is
faithful as a linear representation of the underlying Zorn carrier. Evaluating
the represented operator at the transported unit recovers the element itself.
This is injectivity of the action map; it does not assert multiplicativity of
right regular operators for the nonassociative Zorn product. -/
theorem supercolorRightRegularInThreeMode_injective :
    Function.Injective supercolorRightRegularInThreeMode := by
  intro X Y h
  have h₁ := congrArg
    (fun T : realThreeMatrixGradedTensor =>
      realThreeMatrixTensorOnH4 T
        (supercolorToDoubleKrein
          InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.one)) h
  rw [threeMode_supercolor_rightRegular_action X
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.one,
    threeMode_supercolor_rightRegular_action Y
      InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.one] at h₁
  rw [InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.one_mul X,
    InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.one_mul Y] at h₁
  exact supercolorToDoubleKrein.injective h₁

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

set_option maxRecDepth 4096
/-- The real three-factor Koszul tensor, the exterior-Fock action, and the
Peirce-supercolor right-regular action agree on each positive circular root.
This composes the matrix representation and the Fock/Zorn equivalence; it
does not identify either associative operator product with the nonassociative
Zorn product. -/
theorem threeMode_supercolor_rootPlus_intertwines_exterior
    (i : Fin 3)
    (ψ : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3) :
    realThreeMatrixTensorOnH4
        (supercolorRightRegularInThreeMode
          (canonicalZornToSupercolor (rootPlus i)))
        (realThreeExteriorToH4 ψ) =
      realThreeExteriorToH4
        (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
          (modeVector i) ψ) := by
  have h := threeMode_supercolor_rightRegular_action
    (canonicalZornToSupercolor (rootPlus i))
    (canonicalZornToSupercolor (fockBdGEquiv ψ))
  have hx : supercolorToCanonicalZorn (canonicalZornToSupercolor (rootPlus i)) =
      rootPlus i := supercolorToCanonicalZorn_canonical _
  have hy : supercolorToDoubleKrein (canonicalZornToSupercolor (fockBdGEquiv ψ)) =
      realThreeExteriorToH4 ψ := by
    rw [supercolorToDoubleKrein_apply, supercolorToCanonicalZorn_canonical]
    rfl
  have hFock := rightRegularOnDoubleKrein_intertwines_fock i ψ
  calc
    realThreeMatrixTensorOnH4
        (supercolorRightRegularInThreeMode
          (canonicalZornToSupercolor (rootPlus i)))
        (realThreeExteriorToH4 ψ) =
      realThreeMatrixTensorOnH4
        (supercolorRightRegularInThreeMode
          (canonicalZornToSupercolor (rootPlus i)))
        (supercolorToDoubleKrein (canonicalZornToSupercolor (fockBdGEquiv ψ))) := by
          rw [hy]
    _ = supercolorToDoubleKrein
          (ZornAlgebra.mul (canonicalZornToSupercolor (fockBdGEquiv ψ))
            (canonicalZornToSupercolor (rootPlus i))) := h
    _ = rightRegularOnDoubleKrein (rootPlus i) (realThreeExteriorToH4 ψ) := by
          rw [supercolor_rightRegular_action, hx, hy]
    _ = zornToDoubleKrein
          (fockBdGEquiv
            (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
              (modeVector i) ψ)) := hFock
    _ = realThreeExteriorToH4
          (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
            (modeVector i) ψ) := rfl

/-- The negative circular root acts as exterior contraction through the same
real Koszul-graded three-factor representation. Thus the Zorn root pair and
the real exterior creation/annihilation pair are identified as operators on
the shared doubled-Krein carrier. -/
theorem threeMode_supercolor_rootMinus_intertwines_exterior
    (i : Fin 3)
    (ψ : InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3) :
    realThreeMatrixTensorOnH4
        (supercolorRightRegularInThreeMode
          (canonicalZornToSupercolor (rootMinus i)))
        (realThreeExteriorToH4 ψ) =
      realThreeExteriorToH4
        (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorContract3
          (modeCovector i) ψ) := by
  have h := threeMode_supercolor_rightRegular_action
    (canonicalZornToSupercolor (rootMinus i))
    (canonicalZornToSupercolor (fockBdGEquiv ψ))
  have hx : supercolorToCanonicalZorn (canonicalZornToSupercolor (rootMinus i)) =
      rootMinus i := supercolorToCanonicalZorn_canonical _
  have hy : supercolorToDoubleKrein (canonicalZornToSupercolor (fockBdGEquiv ψ)) =
      realThreeExteriorToH4 ψ := by
    rw [supercolorToDoubleKrein_apply, supercolorToCanonicalZorn_canonical]
    rfl
  have hFock := rightRegularOnDoubleKrein_intertwines_fock_annihilation i ψ
  calc
    realThreeMatrixTensorOnH4
        (supercolorRightRegularInThreeMode
          (canonicalZornToSupercolor (rootMinus i)))
        (realThreeExteriorToH4 ψ) =
      realThreeMatrixTensorOnH4
        (supercolorRightRegularInThreeMode
          (canonicalZornToSupercolor (rootMinus i)))
        (supercolorToDoubleKrein (canonicalZornToSupercolor (fockBdGEquiv ψ))) := by
          rw [hy]
    _ = supercolorToDoubleKrein
          (ZornAlgebra.mul (canonicalZornToSupercolor (fockBdGEquiv ψ))
            (canonicalZornToSupercolor (rootMinus i))) := h
    _ = rightRegularOnDoubleKrein (rootMinus i) (realThreeExteriorToH4 ψ) := by
          rw [supercolor_rightRegular_action, hx, hy]
    _ = zornToDoubleKrein
          (fockBdGEquiv
            (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorContract3
              (modeCovector i) ψ)) := hFock
    _ = realThreeExteriorToH4
          (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorContract3
            (modeCovector i) ψ) := rfl

end InfoGeometry.Superalgebra.RealGradedZornCARBridge

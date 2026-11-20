/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Canonical.SuperGrassmannianFiveGradedEightByEight
import InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge

/-!
# Real graded-tensor bridge for the five-graded Fock superalgebra

The five-graded Fock owner uses real `8 × 8` matrices. The Hestenes/Krein
owner uses the native three-factor Koszul-graded tensor product of real
`2 × 2` matrix factors. Existing owner equivalences identify both with
operators on the same doubled real Krein carrier. This module transports the
actual superbracket, CAR relations, and Peirce supercolor right-regular action
through those equivalences. It does not identify associative operator
composition with nonassociative Zorn multiplication.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge

open InfoGeometry.Canonical.RealSolderingWeylKreinBridge
open InfoGeometry.Canonical.SuperGrassmannianFiveGradedEightByEight

abbrev TensorCarrier := realThreeMatrixGradedTensor
abbrev FockCarrier := Matrix (Fin 8) (Fin 8) ℝ
abbrev KreinOperatorCarrier := Module.End ℝ
  InfoGeometry.Canonical.RealDoubledChiralKreinFrame.KreinFrame4

/-- The real algebra equivalence from five-graded Fock matrices to the
three-mode Koszul-graded tensor algebra. -/
def fockMatrixToRealGradedTensor : FockCarrier ≃ₐ[ℝ] TensorCarrier :=
  realThreeMatrixTensorToFin8.symm

/-- The real algebra equivalence from five-graded Fock matrices to operators
on the doubled real Krein carrier. -/
def fockMatrixToKreinOperator : FockCarrier ≃ₐ[ℝ] KreinOperatorCarrier :=
  fockMatrixToRealGradedTensor.trans realThreeMatrixTensorOnH4

/-- Superbracket on the three-mode graded tensor algebra with the same parity
convention as the five-graded Fock owner. -/
def tensorSuperBracket (p q : Z2Grade) (A B : TensorCarrier) : TensorCarrier :=
  match p, q with
  | .odd, .odd => A * B + B * A
  | _, _ => A * B - B * A

/-- The superbracket is preserved by the real Fock-to-graded-tensor algebra
equivalence. -/
theorem fockMatrixToRealGradedTensor_superBracket
    (p q : Z2Grade) (A B : FockCarrier) :
    fockMatrixToRealGradedTensor (superBracketR p q A B) =
      tensorSuperBracket p q (fockMatrixToRealGradedTensor A)
        (fockMatrixToRealGradedTensor B) := by
  cases p <;> cases q <;>
    simp [superBracketR, tensorSuperBracket, map_add, map_sub, map_mul]

/-- The superbracket is preserved through the represented action on the
doubled real Krein carrier. -/
theorem fockMatrixToKreinOperator_superBracket
    (p q : Z2Grade) (A B : FockCarrier) :
    fockMatrixToKreinOperator (superBracketR p q A B) =
      match p, q with
      | .odd, .odd =>
          fockMatrixToKreinOperator A * fockMatrixToKreinOperator B +
            fockMatrixToKreinOperator B * fockMatrixToKreinOperator A
      | _, _ =>
          fockMatrixToKreinOperator A * fockMatrixToKreinOperator B -
            fockMatrixToKreinOperator B * fockMatrixToKreinOperator A := by
  cases p <;> cases q <;>
    simp [fockMatrixToKreinOperator, superBracketR, map_add, map_sub, map_mul]

/-- The grade `+1` Fock creation family represented on the doubled Krein
carrier. -/
def fockCreationOnKrein (i : Fin 3) : KreinOperatorCarrier :=
  fockMatrixToKreinOperator (gPlus1R i)

/-- The grade `-1` Fock annihilation family represented on the doubled
Krein carrier. -/
def fockAnnihilationOnKrein (i : Fin 3) : KreinOperatorCarrier :=
  fockMatrixToKreinOperator (gMinus1R i)

/-- The five-graded Fock CAR relation holds exactly after transport to
operators on the doubled real Krein space. -/
theorem fockCreationAnnihilationOnKrein_CAR (i j : Fin 3) :
    fockCreationOnKrein i * fockAnnihilationOnKrein j +
        fockAnnihilationOnKrein j * fockCreationOnKrein i =
      (if i = j then (1 : ℝ) else 0) • (1 : KreinOperatorCarrier) := by
  have hZ := gPlus1_gMinus1_odd_superBracketZ i j
  have hR := congrArg ((Int.castRingHom ℝ).mapMatrix) hZ
  rw [mapMatrix_superBracketZ, mapMatrix_zsmul] at hR
  have hCAR : superBracketR .odd .odd (gPlus1R i) (gMinus1R j) =
      (if i = j then (1 : ℝ) else 0) • (1 : FockCarrier) := by
    simpa [gPlus1R, gMinus1R, gPlus1Z, gMinus1Z] using hR
  have hCARsum : gPlus1R i * gMinus1R j + gMinus1R j * gPlus1R i =
      (if i = j then (1 : ℝ) else 0) • (1 : FockCarrier) := by
    simpa [superBracketR] using hCAR
  simp only [fockCreationOnKrein, fockAnnihilationOnKrein]
  rw [← map_mul, ← map_mul, ← map_add, hCARsum, map_smul, map_one]

/-- The grade `+2` Fock bivector creation family represented on the doubled
Krein carrier. -/
def fockBivectorCreationOnKrein (p : Fin 3) : KreinOperatorCarrier :=
  fockMatrixToKreinOperator (gPlus2R p)

/-- The transported grade `+2` generator is the ordered product of its two
grade `+1` creation generators. -/
theorem fockBivectorCreationOnKrein_eq (p : Fin 3) :
    fockBivectorCreationOnKrein p =
      fockCreationOnKrein (bivectorPair p).1 *
        fockCreationOnKrein (bivectorPair p).2 := by
  simp [fockBivectorCreationOnKrein, fockCreationOnKrein, gPlus2R,
    gPlus2Z, gPlus1R, gPlus1Z, map_mul, fockMatrixToKreinOperator]

/-- A Peirce supercolor right-regular operator expressed in the graded tensor
algebra. The representative is obtained by the inverse of the faithful
Krein-operator equivalence. -/
def supercolorRightRegularAsGradedTensor
    (X : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra ℝ) :
    TensorCarrier :=
  realThreeMatrixTensorOnH4.symm
    (InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein
      (InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn X))

/-- The tensor representative acts by exactly the owner's nonassociative
Zorn right-regular action on the doubled Krein carrier. -/
theorem supercolorRightRegularAsGradedTensor_spec
    (X : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra ℝ) :
    realThreeMatrixTensorOnH4 (supercolorRightRegularAsGradedTensor X) =
      InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein
        (InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn X) := by
  simp [supercolorRightRegularAsGradedTensor]

/-- Zorn multiplication followed by the doubled-Krein carrier equivalence
agrees with the represented right-regular action. This retains the Zorn
owner's order and makes no associativity claim. -/
theorem supercolor_product_action_in_fock_matrix_coordinates
    (X Y : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra ℝ) :
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToDoubleKrein
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.mul Y X) =
      realThreeMatrixTensorOnH4
        (supercolorRightRegularAsGradedTensor X)
        (InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToDoubleKrein Y) := by
  rw [supercolorRightRegularAsGradedTensor_spec]
  exact InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolor_rightRegular_action X Y

end InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge

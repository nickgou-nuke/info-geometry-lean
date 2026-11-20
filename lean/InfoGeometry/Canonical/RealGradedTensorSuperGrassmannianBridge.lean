/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Canonical.SuperGrassmannianFiveGradedEightByEight
import InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge
import InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge
import InfoGeometry.Superalgebra.RealGradedZornCARBridge

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

/-! ### Circular root channels as real Majorana pairs

The circular Peirce creation/annihilation roots are transported to the same
three-factor real Koszul tensor by the right-regular action. Their real sum
and difference give a concrete split-Clifford pair in each channel. -/

/-- The positive circular root represented in the real graded tensor algebra. -/
def circularRootPlusInTensor (i : Fin 3) : TensorCarrier :=
  InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode
    (InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.canonicalZornToSupercolor
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i))

/-- The negative circular root represented in the real graded tensor algebra. -/
def circularRootMinusInTensor (i : Fin 3) : TensorCarrier :=
  InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode
    (InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.canonicalZornToSupercolor
      (InfoGeometry.Lie.SplitOctonionEllPolarization.rootMinus i))

/-- The native graded-tensor representation carries the Peirce-supercolor
Jordan anticommutator to the associative operator anticommutator. The source
product remains the nonassociative split-octonion product; the theorem makes
no multiplicativity claim for the right-regular map. -/
theorem supercolorJordanAnticommutator_in_tensor
    (X Y : InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra ℝ) :
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode
        (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.anticommutator X Y) =
      InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode X *
          InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode Y +
        InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode Y *
          InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode X := by
  simp only [InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode]
  rw [← map_mul, ← map_mul, ← map_add]
  apply congrArg realThreeMatrixTensorOnH4.symm
  rw [InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_anticommutator]
  apply congrArg
    (InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein)
  change InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn
      (InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.mul X Y +
        InfoGeometry.Superalgebra.PeirceDeWittZornQuantization.ZornAlgebra.mul Y X) = _
  rw [map_add,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_mul,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_mul]
  rfl

private theorem circularRootPlusInTensor_square (i : Fin 3) :
    circularRootPlusInTensor i * circularRootPlusInTensor i = 0 := by
  unfold circularRootPlusInTensor
  apply realThreeMatrixTensorOnH4.injective
  rw [map_mul,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical,
    InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_rootPlus_sq,
    map_zero]

private theorem circularRootMinusInTensor_square (i : Fin 3) :
    circularRootMinusInTensor i * circularRootMinusInTensor i = 0 := by
  unfold circularRootMinusInTensor
  apply realThreeMatrixTensorOnH4.injective
  rw [map_mul,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical,
    InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_rootMinus_sq,
    map_zero]

/-- The positive circular roots are mutually odd in the actual three-factor
Koszul tensor of real `2 × 2` matrix algebras. -/
theorem circularRootPlusInTensor_anticommutator (i j : Fin 3) :
    circularRootPlusInTensor i * circularRootPlusInTensor j +
      circularRootPlusInTensor j * circularRootPlusInTensor i = 0 := by
  apply realThreeMatrixTensorOnH4.injective
  rw [map_add, map_mul, map_mul,
    circularRootPlusInTensor, circularRootPlusInTensor,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical]
  rw [map_zero]
  exact InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_creation_anticommutator i j

/-- The negative circular roots are mutually odd in the actual three-factor
Koszul tensor of real `2 × 2` matrix algebras. -/
theorem circularRootMinusInTensor_anticommutator (i j : Fin 3) :
    circularRootMinusInTensor i * circularRootMinusInTensor j +
      circularRootMinusInTensor j * circularRootMinusInTensor i = 0 := by
  apply realThreeMatrixTensorOnH4.injective
  rw [map_add, map_mul, map_mul,
    circularRootMinusInTensor, circularRootMinusInTensor,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical]
  rw [map_zero]
  exact InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_annihilation_anticommutator i j

/-- The complete three-channel creation/annihilation CAR relation is realized
inside the native graded tensor algebra, before representing it on the Krein
space. -/
theorem circularRootInTensor_mixed_CAR (i j : Fin 3) :
    circularRootMinusInTensor j * circularRootPlusInTensor i +
      circularRootPlusInTensor i * circularRootMinusInTensor j =
        if i = j then (1 : TensorCarrier) else 0 := by
  apply realThreeMatrixTensorOnH4.injective
  rw [map_add, map_mul, map_mul,
    circularRootMinusInTensor, circularRootPlusInTensor,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    InfoGeometry.Superalgebra.RealGradedZornCARBridge.supercolorRightRegularInThreeMode,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    realThreeMatrixTensorOnH4.apply_symm_apply,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical,
    InfoGeometry.Superalgebra.RealPeirceZornCarrierBridge.supercolorToCanonicalZorn_canonical]
  have h := InfoGeometry.Krein.SplitOctonionZornRegularH4Bridge.rightRegularOnDoubleKrein_mixed_anticommutator i j
  by_cases hij : i = j
  · simp [hij] at h ⊢
    exact h
  · simp [hij] at h ⊢
    exact h

/-- Real positive-square Majorana generator obtained as the sum of the
negative and positive circular root channels. -/
def circularMajoranaTime (i : Fin 3) : TensorCarrier :=
  circularRootMinusInTensor i + circularRootPlusInTensor i

/-- Real negative-square Majorana generator obtained as the difference of
the negative and positive circular root channels. -/
def circularMajoranaSpace (i : Fin 3) : TensorCarrier :=
  circularRootMinusInTensor i - circularRootPlusInTensor i

/-- Every circular root pair yields a real `Cl(1,1)` pair in the native
Koszul-graded tensor of real `2 × 2` matrix factors. -/
theorem circularMajorana_splitClifford_relations (i : Fin 3) :
    circularMajoranaTime i * circularMajoranaTime i = 1 ∧
    circularMajoranaSpace i * circularMajoranaSpace i = -1 ∧
    circularMajoranaTime i * circularMajoranaSpace i +
      circularMajoranaSpace i * circularMajoranaTime i = 0 := by
  have hm := circularRootMinusInTensor_square i
  have hp := circularRootPlusInTensor_square i
  have hCAR := circularRootInTensor_mixed_CAR i i
  constructor
  · change (circularRootMinusInTensor i + circularRootPlusInTensor i) *
      (circularRootMinusInTensor i + circularRootPlusInTensor i) = 1
    calc
      (circularRootMinusInTensor i + circularRootPlusInTensor i) *
          (circularRootMinusInTensor i + circularRootPlusInTensor i) =
          circularRootMinusInTensor i * circularRootMinusInTensor i +
            (circularRootMinusInTensor i * circularRootPlusInTensor i +
              circularRootPlusInTensor i * circularRootMinusInTensor i) +
            circularRootPlusInTensor i * circularRootPlusInTensor i := by noncomm_ring
        _ = 1 := by rw [hm, hCAR, hp]; norm_num
  · constructor
    · change (circularRootMinusInTensor i - circularRootPlusInTensor i) *
        (circularRootMinusInTensor i - circularRootPlusInTensor i) = -1
      calc
        (circularRootMinusInTensor i - circularRootPlusInTensor i) *
            (circularRootMinusInTensor i - circularRootPlusInTensor i) =
            circularRootMinusInTensor i * circularRootMinusInTensor i -
              (circularRootMinusInTensor i * circularRootPlusInTensor i +
                circularRootPlusInTensor i * circularRootMinusInTensor i) +
              circularRootPlusInTensor i * circularRootPlusInTensor i := by noncomm_ring
        _ = -1 := by rw [hm, hCAR, hp]; norm_num
    · change
        (circularRootMinusInTensor i + circularRootPlusInTensor i) *
            (circularRootMinusInTensor i - circularRootPlusInTensor i) +
          (circularRootMinusInTensor i - circularRootPlusInTensor i) *
            (circularRootMinusInTensor i + circularRootPlusInTensor i) = 0
      calc
        _ = circularRootMinusInTensor i * circularRootMinusInTensor i +
              circularRootMinusInTensor i * circularRootMinusInTensor i -
            (circularRootPlusInTensor i * circularRootPlusInTensor i +
              circularRootPlusInTensor i * circularRootPlusInTensor i) := by noncomm_ring
        _ = 0 := by rw [hm, hp]; norm_num

/-- Distinct circular time Majoranas anticommute in the real graded tensor. -/
theorem circularMajoranaTime_cross_anticommute (i j : Fin 3) (hij : i ≠ j) :
    circularMajoranaTime i * circularMajoranaTime j +
      circularMajoranaTime j * circularMajoranaTime i = 0 := by
  have haa := circularRootMinusInTensor_anticommutator i j
  have hcc := circularRootPlusInTensor_anticommutator i j
  have ham := circularRootInTensor_mixed_CAR j i
  have hma := circularRootInTensor_mixed_CAR i j
  have hji : j ≠ i := Ne.symm hij
  simp [hij, hji] at ham hma
  change (circularRootMinusInTensor i + circularRootPlusInTensor i) *
      (circularRootMinusInTensor j + circularRootPlusInTensor j) +
    (circularRootMinusInTensor j + circularRootPlusInTensor j) *
      (circularRootMinusInTensor i + circularRootPlusInTensor i) = 0
  calc
    _ = (circularRootMinusInTensor i * circularRootMinusInTensor j +
          circularRootMinusInTensor j * circularRootMinusInTensor i) +
        (circularRootMinusInTensor i * circularRootPlusInTensor j +
          circularRootPlusInTensor j * circularRootMinusInTensor i) +
        (circularRootMinusInTensor j * circularRootPlusInTensor i +
          circularRootPlusInTensor i * circularRootMinusInTensor j) +
        (circularRootPlusInTensor i * circularRootPlusInTensor j +
          circularRootPlusInTensor j * circularRootPlusInTensor i) := by noncomm_ring
    _ = 0 := by rw [haa, ham, hma, hcc]; simp

/-- Distinct circular space Majoranas anticommute in the real graded tensor. -/
theorem circularMajoranaSpace_cross_anticommute (i j : Fin 3) (hij : i ≠ j) :
    circularMajoranaSpace i * circularMajoranaSpace j +
      circularMajoranaSpace j * circularMajoranaSpace i = 0 := by
  have haa := circularRootMinusInTensor_anticommutator i j
  have hcc := circularRootPlusInTensor_anticommutator i j
  have ham := circularRootInTensor_mixed_CAR j i
  have hma := circularRootInTensor_mixed_CAR i j
  have hji : j ≠ i := Ne.symm hij
  simp [hij, hji] at ham hma
  change (circularRootMinusInTensor i - circularRootPlusInTensor i) *
      (circularRootMinusInTensor j - circularRootPlusInTensor j) +
    (circularRootMinusInTensor j - circularRootPlusInTensor j) *
      (circularRootMinusInTensor i - circularRootPlusInTensor i) = 0
  calc
    _ = (circularRootMinusInTensor i * circularRootMinusInTensor j +
          circularRootMinusInTensor j * circularRootMinusInTensor i) -
        (circularRootMinusInTensor i * circularRootPlusInTensor j +
          circularRootPlusInTensor j * circularRootMinusInTensor i) -
        (circularRootMinusInTensor j * circularRootPlusInTensor i +
          circularRootPlusInTensor i * circularRootMinusInTensor j) +
        (circularRootPlusInTensor i * circularRootPlusInTensor j +
          circularRootPlusInTensor j * circularRootPlusInTensor i) := by noncomm_ring
    _ = 0 := by rw [haa, ham, hma, hcc]; simp

/-- A time Majorana anticommutes with every space Majorana from a distinct
circular mode in the genuine Koszul-graded matrix tensor. -/
theorem circularMajoranaTimeSpace_cross_anticommute
    (i j : Fin 3) (hij : i ≠ j) :
    circularMajoranaTime i * circularMajoranaSpace j +
      circularMajoranaSpace j * circularMajoranaTime i = 0 := by
  have haa := circularRootMinusInTensor_anticommutator i j
  have hcc := circularRootPlusInTensor_anticommutator i j
  have ham := circularRootInTensor_mixed_CAR j i
  have hma := circularRootInTensor_mixed_CAR i j
  have hji : j ≠ i := Ne.symm hij
  simp [hij, hji] at ham hma
  change (circularRootMinusInTensor i + circularRootPlusInTensor i) *
      (circularRootMinusInTensor j - circularRootPlusInTensor j) +
    (circularRootMinusInTensor j - circularRootPlusInTensor j) *
      (circularRootMinusInTensor i + circularRootPlusInTensor i) = 0
  calc
    _ = (circularRootMinusInTensor i * circularRootMinusInTensor j +
          circularRootMinusInTensor j * circularRootMinusInTensor i) -
        (circularRootMinusInTensor i * circularRootPlusInTensor j +
          circularRootPlusInTensor j * circularRootMinusInTensor i) +
        (circularRootMinusInTensor j * circularRootPlusInTensor i +
          circularRootPlusInTensor i * circularRootMinusInTensor j) -
        (circularRootPlusInTensor i * circularRootPlusInTensor j +
          circularRootPlusInTensor j * circularRootPlusInTensor i) := by noncomm_ring
    _ = 0 := by rw [haa, ham, hma, hcc]; simp

/-- The circular real Majoranas in the three-factor graded tensor satisfy the
`Cl(3,3)` anticommutation law on their six signed generators. -/
theorem circularMajorana_threeMode_Clifford_relations (i j : Fin 3) :
    circularMajoranaTime i * circularMajoranaTime j +
        circularMajoranaTime j * circularMajoranaTime i =
      (if i = j then (2 : ℝ) else 0) • (1 : TensorCarrier) ∧
    circularMajoranaSpace i * circularMajoranaSpace j +
        circularMajoranaSpace j * circularMajoranaSpace i =
      (if i = j then (-2 : ℝ) else 0) • (1 : TensorCarrier) ∧
    circularMajoranaTime i * circularMajoranaSpace j +
        circularMajoranaSpace j * circularMajoranaTime i = 0 := by
  by_cases hij : i = j
  · subst j
    obtain ⟨ht, hs, hts⟩ := circularMajorana_splitClifford_relations i
    constructor
    · rw [ht]
      norm_num [two_smul]
    constructor
    · rw [hs]
      norm_num [two_smul]
    · exact hts
  · constructor
    · simp [hij, circularMajoranaTime_cross_anticommute i j hij]
    constructor
    · simp [hij, circularMajoranaSpace_cross_anticommute i j hij]
    · exact circularMajoranaTimeSpace_cross_anticommute i j hij

end InfoGeometry.Canonical.RealGradedTensorSuperGrassmannianBridge

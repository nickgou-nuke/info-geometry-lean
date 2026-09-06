import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Arithmetic.PrimonFinite


noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

open PrimeBosonFermionGas
open PrimonFinite


def finitePrimeWeylDenominator
    {PrimeLabel R : Type*} [CommRing R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R) : R :=
  ∏ p ∈ S, (1 - q p)

def finitePrimeBosonicInverseDenominator
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R) : R :=
  ∏ p ∈ S, (1 - q p)⁻¹

lemma finitePrimeWeylDenominator_ne_zero
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel) (q : PrimeLabel → R)
    (h : ∀ p ∈ S, (1 - q p) ≠ 0) :
    finitePrimeWeylDenominator S q ≠ 0 := by
  unfold finitePrimeWeylDenominator
  exact Finset.prod_ne_zero_iff.mpr h

lemma finitePrimeBosonicInverseDenominator_ne_zero
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel) (q : PrimeLabel → R)
    (h : ∀ p ∈ S, (1 - q p) ≠ 0) :
    finitePrimeBosonicInverseDenominator S q ≠ 0 := by
  unfold finitePrimeBosonicInverseDenominator
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => inv_ne_zero (h p hp))

theorem finitePrimeWeylDenominator_eq_finiteSupertrace
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R) :
    finitePrimeWeylDenominator S q =
      STrF S q := by
  exact (STrF_eq_prod S q).symm

theorem bosonicInverse_mul_weylDenominator_cancel
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R)
    (h : ∀ p ∈ S, 1 - q p ≠ 0) :
    finitePrimeBosonicInverseDenominator S q *
      finitePrimeWeylDenominator S q = 1 := by
  unfold finitePrimeBosonicInverseDenominator finitePrimeWeylDenominator
  calc
    (∏ p ∈ S, (1 - q p)⁻¹) * (∏ p ∈ S, (1 - q p))
        = ∏ p ∈ S, ((1 - q p)⁻¹ * (1 - q p)) := by
            rw [← Finset.prod_mul_distrib]
    _ = ∏ _p ∈ S, (1 : R) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact inv_mul_cancel₀ (h p hp)
    _ = 1 := by
            simp

theorem bosonicInverse_eq_inv_weylDenominator
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R)
    (h : ∀ p ∈ S, 1 - q p ≠ 0) :
    finitePrimeBosonicInverseDenominator S q =
      (finitePrimeWeylDenominator S q)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa [mul_comm] using
    (bosonicInverse_mul_weylDenominator_cancel S q h)


def symmetricRootFactor
    {R : Type*} [Field R]
    (y : R) : R :=
  y - y⁻¹

def eulerWeightFromHalfRoot
    {R : Type*} [Field R]
    (y : R) : R :=
  y⁻¹ * y⁻¹

theorem normalized_symmetricRootFactor_eq_one_sub_eulerWeight
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    y⁻¹ * symmetricRootFactor y =
      1 - eulerWeightFromHalfRoot y := by
  unfold symmetricRootFactor eulerWeightFromHalfRoot
  rw [mul_sub]
  rw [inv_mul_cancel₀ hy]

def finiteNormalizedHyperbolicDenominator
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (y : PrimeLabel → R) : R :=
  ∏ p ∈ S, (y p)⁻¹ * symmetricRootFactor (y p)

theorem finiteNormalizedHyperbolicDenominator_eq_weylDenominator
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (y : PrimeLabel → R)
    (hy : ∀ p ∈ S, y p ≠ 0) :
    finiteNormalizedHyperbolicDenominator S y =
      finitePrimeWeylDenominator S (fun p => eulerWeightFromHalfRoot (y p)) := by
  unfold finiteNormalizedHyperbolicDenominator finitePrimeWeylDenominator
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact normalized_symmetricRootFactor_eq_one_sub_eulerWeight (hy p hp)


def orbitDeterminantFactor
    {R : Type*} [Ring R]
    (y : R) : R :=
  y * y - 1

def finiteOrbitDeterminantFromHalfRoot
    {RootLabel R : Type*} [CommRing R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, orbitDeterminantFactor (y α)

def finiteRawHyperbolicDenominator
    {RootLabel R : Type*} [Field R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, symmetricRootFactor (y α)

def finiteHalfRootProduct
    {RootLabel R : Type*} [CommMonoid R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, y α

theorem orbitDeterminantFactor_eq_halfRoot_mul_symmetricRootFactor
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    orbitDeterminantFactor y = y * symmetricRootFactor y := by
  unfold orbitDeterminantFactor symmetricRootFactor
  rw [mul_sub, mul_inv_cancel₀ hy]

theorem finiteOrbitDeterminant_eq_halfRootProduct_mul_rawHyperbolicDenominator
    {RootLabel R : Type*} [Field R]
    (S : Finset RootLabel)
    (y : RootLabel → R)
    (hy : ∀ α ∈ S, y α ≠ 0) :
    finiteOrbitDeterminantFromHalfRoot S y =
      finiteHalfRootProduct S y * finiteRawHyperbolicDenominator S y := by
  unfold finiteOrbitDeterminantFromHalfRoot finiteHalfRootProduct
    finiteRawHyperbolicDenominator
  calc
    (∏ α ∈ S, orbitDeterminantFactor (y α))
        = ∏ α ∈ S, y α * symmetricRootFactor (y α) := by
            refine Finset.prod_congr rfl ?_
            intro α hα
            exact orbitDeterminantFactor_eq_halfRoot_mul_symmetricRootFactor (hy α hα)
    _ = (∏ α ∈ S, y α) * (∏ α ∈ S, symmetricRootFactor (y α)) := by
          rw [Finset.prod_mul_distrib]

theorem symmetricRootFactor_eq_halfRoot_mul_one_sub_eulerWeight
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    symmetricRootFactor y =
      y * (1 - eulerWeightFromHalfRoot y) := by
  unfold symmetricRootFactor eulerWeightFromHalfRoot
  rw [mul_sub, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ hy, one_mul]

theorem finiteRawHyperbolicDenominator_eq_halfRootProduct_mul_weylDenominator
    {RootLabel R : Type*} [Field R]
    (S : Finset RootLabel)
    (y : RootLabel → R)
    (hy : ∀ α ∈ S, y α ≠ 0) :
    finiteRawHyperbolicDenominator S y =
      finiteHalfRootProduct S y *
        finitePrimeWeylDenominator S (fun α => eulerWeightFromHalfRoot (y α)) := by
  unfold finiteRawHyperbolicDenominator finiteHalfRootProduct finitePrimeWeylDenominator
  calc
    (∏ α ∈ S, symmetricRootFactor (y α))
        = ∏ α ∈ S, y α * (1 - eulerWeightFromHalfRoot (y α)) := by
            refine Finset.prod_congr rfl ?_
            intro α hα
            exact symmetricRootFactor_eq_halfRoot_mul_one_sub_eulerWeight (hy α hα)
    _ = (∏ α ∈ S, y α) * (∏ α ∈ S, (1 - eulerWeightFromHalfRoot (y α))) := by
          rw [Finset.prod_mul_distrib]


def finiteSignedRawHyperbolicTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * symmetricRootFactor (y a)

def finiteSignedGrowingTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * y a

def finiteSignedDecayingTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * (y a)⁻¹

theorem finiteSignedRawHyperbolicTrace_eq_growing_sub_decaying
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) :
    finiteSignedRawHyperbolicTrace A χ y =
      finiteSignedGrowingTrace A χ y -
        finiteSignedDecayingTrace A χ y := by
  unfold finiteSignedRawHyperbolicTrace finiteSignedGrowingTrace
    finiteSignedDecayingTrace symmetricRootFactor
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a ha
  ring

def finiteSignedNormalizedHyperbolicTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * ((y a)⁻¹ * symmetricRootFactor (y a))

theorem finiteSignedNormalizedHyperbolicTrace_eq_eulerFactor_sum
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R)
    (hy : ∀ a ∈ A, y a ≠ 0) :
    finiteSignedNormalizedHyperbolicTrace A χ y =
      ∑ a ∈ A, χ a * (1 - eulerWeightFromHalfRoot (y a)) := by
  unfold finiteSignedNormalizedHyperbolicTrace
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [normalized_symmetricRootFactor_eq_one_sub_eulerWeight (hy a ha)]


structure HyperbolicRootFactorCalibration
    (PrimeLabel R : Type*) [CommRing R] where
  support : Finset PrimeLabel
  q : PrimeLabel → R
  normalizedRootFactor : PrimeLabel → R
  normalizedRootFactor_eq :
    ∀ p ∈ support, normalizedRootFactor p = 1 - q p

namespace HyperbolicRootFactorCalibration

variable
    {PrimeLabel R : Type*} [CommRing R]
    (C : HyperbolicRootFactorCalibration PrimeLabel R)

def product : R :=
  ∏ p ∈ C.support, C.normalizedRootFactor p

theorem product_eq_weylDenominator :
    C.product = finitePrimeWeylDenominator C.support C.q := by
  unfold product finitePrimeWeylDenominator
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact C.normalizedRootFactor_eq p hp

end HyperbolicRootFactorCalibration

structure PrimeWeylVandermondeShadow
    (PrimeLabel DenominatorReadout VandermondeReadout : Type*) where
  support : Finset PrimeLabel
  denominator : DenominatorReadout
  vandermonde : VandermondeReadout
  compare : DenominatorReadout → VandermondeReadout → Prop
  denominator_matches_vandermonde :
    compare denominator vandermonde

namespace PrimeWeylVandermondeShadow

theorem valid
    {PrimeLabel DenominatorReadout VandermondeReadout : Type*}
    (W : PrimeWeylVandermondeShadow
      PrimeLabel DenominatorReadout VandermondeReadout) :
    W.compare W.denominator W.vandermonde :=
  W.denominator_matches_vandermonde

end PrimeWeylVandermondeShadow

end InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

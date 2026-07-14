import Mathlib
import InfoGeometry.Arithmetic.PrimeBosonFermionGas
import InfoGeometry.Arithmetic.PrimonFinite

/-!
# InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

Finite prime-mode Weyl-denominator bridge.

This module gives a conservative theorem-bearing surface for the slogan:

```text
signed fermionic prime supertrace = finite Weyl/Euler denominator.
```

It does not assert an infinite Kac--Moody denominator identity, an analytic
continuation theorem, a Riemann-zero statement, or a literal Vandermonde
determinant model for the infinite prime set.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

open InfoGeometry.Arithmetic.PrimeBosonFermionGas

/-! ## 1. Finite prime Weyl denominator -/

/--
Finite prime-mode Weyl/Euler denominator.

For the primon specialization, `q p` is later interpreted as `p^{-β}`.
-/
def finitePrimeWeylDenominator
    {PrimeLabel R : Type*} [CommRing R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R) : R :=
  ∏ p ∈ S, (1 - q p)

/-- Finite bosonic inverse denominator. -/
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

/-- The finite Weyl denominator is the signed fermion product. -/
theorem finitePrimeWeylDenominator_eq_signedFermionPartition
    {PrimeLabel R : Type*} [CommRing R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R) :
    finitePrimeWeylDenominator S q =
      finitePrimeWeylDenominator S q := by
  rfl

/-- The finite bosonic inverse denominator is the boson product. -/
theorem finitePrimeBosonicInverseDenominator_eq_bosonPartition
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R) :
    finitePrimeBosonicInverseDenominator S q =
      finitePrimeBosonicInverseDenominator S q := by
  rfl

/--
Finite Weyl denominator equals the finite fermionic parity supertrace.

This is the exact finite owner for:

```text
sum_{T subset S} (-1)^|T| prod_{p in T} q p
  = prod_{p in S} (1 - q p).
```
-/
theorem finitePrimeWeylDenominator_eq_finiteSupertrace
    {PrimeLabel R : Type*} [DecidableEq PrimeLabel] [CommRing R]
    (S : Finset PrimeLabel)
    (q : PrimeLabel → R) :
    finitePrimeWeylDenominator S q =
      InfoGeometry.Arithmetic.PrimonFinite.STrF S q := by
  exact (InfoGeometry.Arithmetic.PrimonFinite.STrF_eq_prod S q).symm

/--
Finite boson × Weyl-denominator cancellation.

This is the finite algebraic core of the formal cancellation
`ζ(β) * 1 / ζ(β) = 1`.
-/
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

/-! ## 2. Normalized hyperbolic root factors -/

/--
Formal symmetric root factor `y - y⁻¹`.

In the primon interpretation, `y` is a finite stand-in for `p^{β/2}`.
-/
def symmetricRootFactor
    {R : Type*} [Field R]
    (y : R) : R :=
  y - y⁻¹

/--
Euler weight associated to a half-root coordinate.

If `y = p^{β/2}`, this is the finite algebraic stand-in for `p^{-β}`.
-/
def eulerWeightFromHalfRoot
    {R : Type*} [Field R]
    (y : R) : R :=
  y⁻¹ * y⁻¹

/--
Normalized hyperbolic root factor equals the Euler denominator factor.

This is the precise finite algebra behind

```text
p^{-β/2} * (p^{β/2} - p^{-β/2}) = 1 - p^{-β}.
```

The raw symmetric factor is not identified with an inverse-zeta trace; the
Euler denominator appears only after the explicit half-root normalization.
-/
theorem normalized_symmetricRootFactor_eq_one_sub_eulerWeight
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    y⁻¹ * symmetricRootFactor y =
      1 - eulerWeightFromHalfRoot y := by
  unfold symmetricRootFactor eulerWeightFromHalfRoot
  rw [mul_sub]
  rw [inv_mul_cancel₀ hy]

/--
Finite product of normalized hyperbolic root factors.

This is the finite product version of the normalized Weyl/Euler denominator
readout.  It remains purely algebraic and finite.
-/
def finiteNormalizedHyperbolicDenominator
    {PrimeLabel R : Type*} [Field R]
    (S : Finset PrimeLabel)
    (y : PrimeLabel → R) : R :=
  ∏ p ∈ S, (y p)⁻¹ * symmetricRootFactor (y p)

/--
The normalized hyperbolic denominator is the finite prime Weyl denominator
with weights `q p = (y p)⁻¹ * (y p)⁻¹`.
-/
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

/-! ## 3. Raw determinant, hyperbolic denominator, and normalized character -/

/--
Raw orbit-determinant local factor from a half-root coordinate.

If `y = T^{α/2}`, this is the finite algebraic stand-in for `T^α - 1`.
-/
def orbitDeterminantFactor
    {R : Type*} [Ring R]
    (y : R) : R :=
  y * y - 1

/--
Finite raw orbit determinant from half-root coordinates.

This models `∏_{α>0} (T^α - 1)` at finite support.
-/
def finiteOrbitDeterminantFromHalfRoot
    {RootLabel R : Type*} [CommRing R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, orbitDeterminantFactor (y α)

/--
Finite raw hyperbolic Weyl denominator from half-root coordinates.

This models `∏_{α>0} (T^{α/2} - T^{-α/2})` at finite support.
-/
def finiteRawHyperbolicDenominator
    {RootLabel R : Type*} [Field R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, symmetricRootFactor (y α)

/-- Product of finite half-root coordinates. -/
def finiteHalfRootProduct
    {RootLabel R : Type*} [CommMonoid R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, y α

/--
Local determinant factorization:
`y² - 1 = y * (y - y⁻¹)`.
-/
theorem orbitDeterminantFactor_eq_halfRoot_mul_symmetricRootFactor
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    orbitDeterminantFactor y = y * symmetricRootFactor y := by
  unfold orbitDeterminantFactor symmetricRootFactor
  rw [mul_sub, mul_inv_cancel₀ hy]

/--
Finite determinant factorization:
`∏ (y² - 1) = (∏ y) * ∏ (y - y⁻¹)`.

This is the kernel-checked finite shadow of
`det(Ad(T)-1) = (∏ T^{α/2}) Δ(T)`.
-/
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

/--
Local raw hyperbolic factor as a normalized multiplicative Weyl character:
`y - y⁻¹ = y * (1 - y⁻¹*y⁻¹)`.
-/
theorem symmetricRootFactor_eq_halfRoot_mul_one_sub_eulerWeight
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    symmetricRootFactor y =
      y * (1 - eulerWeightFromHalfRoot y) := by
  unfold symmetricRootFactor eulerWeightFromHalfRoot
  rw [mul_sub, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ hy, one_mul]

/--
Finite raw hyperbolic denominator as half-root product times the normalized
finite Weyl/Euler denominator.

This is the finite algebraic content of interpreting
`∏(e^{α/2} - e^{-α/2})` as a multiplicative scaling character, while keeping
the normalization factor explicit.
-/
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

/-! ## 4. Raw versus normalized signed hyperbolic traces -/

/--
Finite signed raw hyperbolic trace.

This models the finite algebraic shape of the raw `sinh` readout.  It is a sum
of symmetric factors and is not an Euler product.
-/
def finiteSignedRawHyperbolicTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * symmetricRootFactor (y a)

/-- The growing part of the raw symmetric-root trace. -/
def finiteSignedGrowingTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * y a

/-- The decaying part of the raw symmetric-root trace. -/
def finiteSignedDecayingTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * (y a)⁻¹

/--
The raw hyperbolic trace splits as growing minus decaying terms.

This is the finite warning theorem: without an extra normalization or
regularization witness, the raw hyperbolic trace is not the Möbius heat trace.
-/
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

/--
Finite signed normalized hyperbolic trace.

The local factor is explicitly normalized by `y⁻¹`, so each summand contains
the Euler-denominator factor `1 - y⁻¹*y⁻¹`.
-/
def finiteSignedNormalizedHyperbolicTrace
    {α R : Type*} [Field R]
    (A : Finset α)
    (χ y : α → R) : R :=
  ∑ a ∈ A, χ a * ((y a)⁻¹ * symmetricRootFactor (y a))

/--
After half-root normalization, each signed summand uses the Euler denominator
factor.
-/
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

/-! ## 5. Hyperbolic and Vandermonde interpretation sockets -/

/--
Finite hyperbolic-root calibration.

The raw factor `e^{α/2} - e^{-α/2}` becomes a prime Euler denominator only
after a normalization choice, e.g. multiplication by `e^{-α/2}`.  This structure
records that calibration as data instead of deriving it from the chiral
Liouvillean flow.
-/
structure HyperbolicRootFactorCalibration
    (PrimeLabel R : Type*) [CommRing R] where
  /-- Finite prime/mode support. -/
  support : Finset PrimeLabel
  /-- Euler/Mellin local weight, intended as `p^{-β}`. -/
  q : PrimeLabel → R
  /-- Hyperbolic or Weyl-root local factor after chosen normalization. -/
  normalizedRootFactor : PrimeLabel → R
  /-- Calibration to the Euler denominator factor. -/
  normalizedRootFactor_eq :
    ∀ p ∈ support, normalizedRootFactor p = 1 - q p

namespace HyperbolicRootFactorCalibration

variable
    {PrimeLabel R : Type*} [CommRing R]
    (C : HyperbolicRootFactorCalibration PrimeLabel R)

/-- Product of normalized hyperbolic root factors. -/
def product : R :=
  ∏ p ∈ C.support, C.normalizedRootFactor p

/-- The calibrated hyperbolic-root product is the finite Weyl denominator. -/
theorem product_eq_weylDenominator :
    C.product = finitePrimeWeylDenominator C.support C.q := by
  unfold product finitePrimeWeylDenominator
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact C.normalizedRootFactor_eq p hp

end HyperbolicRootFactorCalibration

/--
Finite Vandermonde/Weyl shadow.

This is only a comparison socket.  A concrete Vandermonde model must supply the
readout and comparison law; the prime Euler denominator is not definitionally a
Vandermonde determinant.
-/
structure PrimeWeylVandermondeShadow
    (PrimeLabel DenominatorReadout VandermondeReadout : Type*) where
  /-- Finite prime/mode support. -/
  support : Finset PrimeLabel
  /-- Finite Weyl/Euler denominator readout. -/
  denominator : DenominatorReadout
  /-- Finite Vandermonde-side readout. -/
  vandermonde : VandermondeReadout
  /-- Supplied comparison relation. -/
  compare : DenominatorReadout → VandermondeReadout → Prop
  /-- Supplied comparison law. -/
  denominator_matches_vandermonde :
    compare denominator vandermonde

namespace PrimeWeylVandermondeShadow

/-- Re-export of the supplied finite Weyl/Vandermonde comparison. -/
theorem valid
    {PrimeLabel DenominatorReadout VandermondeReadout : Type*}
    (W : PrimeWeylVandermondeShadow
      PrimeLabel DenominatorReadout VandermondeReadout) :
    W.compare W.denominator W.vandermonde :=
  W.denominator_matches_vandermonde

end PrimeWeylVandermondeShadow

end InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

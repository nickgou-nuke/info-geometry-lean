import Mathlib.Tactic
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.LinearAlgebra.RootSystem.RootPositive
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Complex.Basic
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.WeylA1Character

open Complex
open MeasureTheory

noncomputable section

/-!
# Weyl Integration Formula and Character Formula

Formalization of the Weyl integration formula for a compact connected Lie group G
with maximal torus T:

  ∫_G f(g) dg = (1/|W|) ∫_T f(t) |δ(t)|² dt

where W = N_G(T)/T is the Weyl group and

  δ(t) = ∏_{α > 0} (e^{α(t)/2} - e^{-α(t)/2})

is the Weyl denominator.

## References

* Adams, J. F. (1982). Lectures on Lie Groups. University of Chicago Press. Theorem 6.1.
* Weyl, Hermann. The classical groups.
* Brocker, Theodor; tom Dieck, Tammo. Representations of compact Lie groups. GTM 98.

## Status

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals.]

- `weylDenominator_nonzero_on_regular`: δ(t) ≠ 0 for regular t ∈ T.
- `finitePrimeWeylDenominatorFormula`: finite product/alternating-sum Weyl denominator.
- `finiteOrbitDeterminantFactorization`: finite determinant factorization through the raw
  hyperbolic denominator.
- `a1CharacterFormula`: rank-one Weyl character cancellation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
[Theorems that compile from explicitly named theorem parameters.]

- `weylIntegrationFormula_of_explicit_changeOfVariables`
- `weylCharacterFormula_of_explicit_alternating_identity`

#### BUCKET 3: OPEN CLOSURE DEBT
[Exact theorem statements that remain unproved.]

- The Weyl integration formula itself.
- The change-of-variables theorem for q: G/T × T → G.
- The Jacobian determinant identity det(Ad_{g/𝔱}(t⁻¹) - I) = |δ(t)|².
- The Weyl character formula as a corollary.
-/

namespace WeylIntegration

/-! ## 1. Weyl denominator δ(t) -/

/--
Structure bundling the data needed for the Weyl integration formula:
a compact connected Lie group G, a maximal torus T, and the root system of (G, T).
-/
structure WeylData (G T : Type*) [Group G] [Group T] where
  positiveRoots : Finset (T → ℂ)
  weylOrder : ℕ
  sign : G → ℤ
  weylAction : G → T → T

/--
The Weyl denominator at t ∈ T:

  δ(t) = ∏_{α > 0} (e^{α(t)/2} - e^{-α(t)/2})
-/
noncomputable def weylDenominator {G T : Type*} [Group G] [Group T]
    (d : WeylData G T) (t : T) : ℂ :=
  Finset.prod d.positiveRoots fun α =>
    (Real.exp ((α t).re / 2) - Real.exp (-(α t).re / 2))

/--
If α(t) ≠ 0 for all positive roots α, then δ(t) ≠ 0.
-/
theorem weylDenominator_nonzero_on_regular {G T : Type*} [Group G] [Group T]
    (d : WeylData G T) (t : T) (hreg : ∀ α ∈ d.positiveRoots, (α t).re ≠ 0) :
    weylDenominator d t ≠ 0 := by
  intro hzero
  dsimp [weylDenominator] at hzero
  rcases Finset.prod_eq_zero_iff.mp hzero with ⟨α, hα, hzeroα⟩
  have : Real.exp ((α t).re / 2) = Real.exp (-(α t).re / 2) := by
    have : (Real.exp ((α t).re / 2) - Real.exp (-(α t).re / 2) : ℂ) = 0 := hzeroα
    exact_mod_cast sub_eq_zero.mp this
  have h_eq : (α t).re / 2 = -(α t).re / 2 :=
    Real.exp_injective this
  have : (α t).re = 0 := by linarith
  exact hreg α hα this

/-! ## 2. Finite constructive owner-backed replacements -/

theorem finitePrimeWeylDenominatorFormula
    (L : InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice)
    (x : ℕ → ℝ) :
    InfoGeometry.Canonical.FormalPrimeRootSystem.weylDenominatorProduct L x =
      InfoGeometry.Canonical.FormalPrimeRootSystem.weylAlternatingSum L x :=
  InfoGeometry.Canonical.FormalPrimeRootSystem.finite_prime_weyl_denominator L x

def orbitDeterminantFactor {R : Type*} [Ring R] (y : R) : R :=
  y * y - 1

def symmetricRootFactor {R : Type*} [Field R] (y : R) : R :=
  y - y⁻¹

def finiteOrbitDeterminantFromHalfRoot
    {RootLabel R : Type*} [CommRing R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, orbitDeterminantFactor (y α)

def finiteHalfRootProduct
    {RootLabel R : Type*} [CommMonoid R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, y α

def finiteRawHyperbolicDenominator
    {RootLabel R : Type*} [Field R]
    (S : Finset RootLabel)
    (y : RootLabel → R) : R :=
  ∏ α ∈ S, symmetricRootFactor (y α)

theorem orbitDeterminantFactor_eq_halfRoot_mul_symmetricRootFactor
    {R : Type*} [Field R]
    {y : R} (hy : y ≠ 0) :
    orbitDeterminantFactor y = y * symmetricRootFactor y := by
  unfold orbitDeterminantFactor symmetricRootFactor
  rw [mul_sub, mul_inv_cancel₀ hy]

theorem finiteOrbitDeterminantFactorization
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

def a1CharacterSum {R : Type*} [Semiring R] (x y : R) (m : ℕ) : R :=
  Finset.sum (Finset.range (m + 1)) (fun i => x ^ i * y ^ (m - i))

def a1Denominator {R : Type*} [Ring R] (x y : R) : R :=
  x - y

theorem a1CharacterFormula
    {R : Type*} [CommRing R]
    (x y : R) (m : ℕ) :
    a1CharacterSum x y m * a1Denominator x y =
      x ^ (m + 1) - y ^ (m + 1) :=
  by
    simpa [a1CharacterSum, a1Denominator, Nat.succ_eq_add_one,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (geom_sum₂_mul x y (m + 1))

/-! ## 3. Weyl integration formula -/

/--
A structure bundling the analytic data: the group G, its maximal torus T,
Haar measures on both, and the covering map q: G/T × T → G.
-/
structure IntegrationData (G T : Type*) [TopologicalSpace G] [Group G] [MeasureSpace G]
    [TopologicalSpace T] [Group T] [MeasureSpace T] extends WeylData G T where
  haarMeasureG : Measure G
  haarMeasureT : Measure T
  /-- The smooth covering map q: G/T × T → G, (gT, t) ↦ gtg⁻¹. -/
  coveringMap : G × T → G

/--
Conditional readback of the Weyl integration formula:

  ∫_G f(g) dg = (1/|W|) ∫_T f(t) |δ(t)|² dt

for any class function f on G, assuming the missing Haar/change-of-variables
and Jacobian theorem as an explicit property.
-/
theorem weylIntegrationFormula_of_explicit_changeOfVariables
    {G T : Type*} [TopologicalSpace G] [Group G] [MeasureSpace G]
    [TopologicalSpace T] [Group T] [MeasureSpace T]
    (d : IntegrationData G T) (f : G → ℂ)
    (_hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (hWeylIntegration :
      (∫ g : G, f g ∂ d.haarMeasureG) =
        (1 / (d.weylOrder : ℂ)) *
          (∫ t : T, f (d.coveringMap (1, t)) *
            (weylDenominator d.toWeylData t * star (weylDenominator d.toWeylData t))
          ∂ d.haarMeasureT)) :
    (∫ g : G, f g ∂ d.haarMeasureG) =
    (1 / (d.weylOrder : ℂ)) *
    (∫ t : T, f (d.coveringMap (1, t)) *
      (weylDenominator d.toWeylData t * star (weylDenominator d.toWeylData t))
    ∂ d.haarMeasureT) :=
  hWeylIntegration

/-! ## 4. Alternating sum and character formula -/

/--
The alternating sum over the Weyl group:

  A_μ(t) = Σ_{w ∈ W} (-1)^{l(w)} e^{w(μ)(t)}
-/
noncomputable def alternatingSum {G T : Type*} [Group G] [Group T]
    (d : WeylData G T) (Wset : Finset G) (mu : T → ℂ) (t : T) : ℂ :=
  Finset.sum Wset fun w => ((d.sign w : ℂ) * mu (d.weylAction w t))

/--
Conditional readback of the Weyl character formula:

  χ|_T(t) · δ(t) = A_{λ + ρ}(t)

The actual rank-one constructive character identity is `a1CharacterFormula`
above.  The general compact-group formula is kept as an explicit property.
-/
theorem weylCharacterFormula_of_explicit_alternating_identity
    {G T : Type*} [TopologicalSpace G] [Group G] [MeasureSpace G]
    [TopologicalSpace T] [Group T] [MeasureSpace T]
    (d : IntegrationData G T) (χ : G → ℂ) (lam : T → ℂ) (Wset : Finset G)
    (_hchar : ∀ g h : G, χ (h * g * h⁻¹) = χ g)
    (t : T)
    (hWeylCharacter :
      χ (d.coveringMap (1, t)) * weylDenominator d.toWeylData t =
        alternatingSum d.toWeylData Wset (fun s => Real.exp (lam s).re) t) :
    χ (d.coveringMap (1, t)) * weylDenominator d.toWeylData t =
      alternatingSum d.toWeylData Wset (fun s => Real.exp (lam s).re) t :=
  hWeylCharacter

end WeylIntegration

import Mathlib
import InfoGeometry.Analysis.LaplaceFourierComparison
import InfoGeometry.Analysis.MellinZetaScaling
import InfoGeometry.Analysis.SpectralTaylorMellinBridge
import InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem

/-!
# InfoGeometry.LanglandsGWBridge

Carrier data for gauge-theoretic reduction in the Langlands--GW layer.

This module does not prove the Atiyah--Bott moment-map theorem or the full
Weyl integration formula. It also does not hide those facts in proof-carrying
data fields. The only closed facts here are the local definitional theorem-owner
readouts attached to the carrier data.
-/

noncomputable section

namespace InfoGeometry

namespace LanglandsGWBridge

open scoped BigOperators FourierTransform RealInnerProductSpace
open InfoGeometry.Analysis.MellinZetaScaling
open InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
open InfoGeometry.Analysis.SpectralTaylorMellinBridge
open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic

/--
Symplectic quotient carrier data for a gauge action.

The fields are intentionally structural:

* `symplecticForm` is the symplectic-geometry carrier;
* `momentumMap` plays the role of a conserved/constraint-valued map `μ`;
* `zeroMomentum` marks the reduction locus `μ = 0`;
* `moduliSpace` is the reduced moduli object exported as carrier data.
* `gaugeAction` is the group action by the provided `Group` parameter.
--/
structure SymplecticQuotientData (Space : Type) (GaugeGroup : Type) [instGroup : Group GaugeGroup] where
  /-- Abstract symplectic-geometry data on the configuration space. -/
  symplecticForm : Type*
  /-- Optional momentum-value type for the moment map. -/
  momentumValue : Type*
  /-- Momentum map `μ : Space → momentumValue`. -/
  momentumMap : Space → momentumValue
  /-- Distinguished zero element in the momentum-value type. -/
  zeroMomentum : momentumValue
  /-- Group action on the configuration space by the provided `Group` parameter. -/
  gaugeAction : GaugeGroup → Space → Space
  /-- Moduli object obtained from the constrained quotient. -/
  moduliSpace : Type*
  /-- The moduli map from constrained points into the quotient object. -/
  moduliProjection : {a : Space // momentumMap a = zeroMomentum} → moduliSpace

/--
Fixed-point locus `μ⁻¹(0)` for the momentum map.
-/
def SymplecticQuotientData.zeroLocus
    {Space GaugeGroup : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData Space GaugeGroup) : Set Space :=
  {a : Space | Q.momentumMap a = Q.zeroMomentum}

/--
Closed local theorem: zero-locus membership is exactly the momentum-map equation.
-/
theorem SymplecticQuotientData.mem_zeroLocus_iff
    {Space GaugeGroup : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData Space GaugeGroup) (a : Space) :
    a ∈ Q.zeroLocus ↔ Q.momentumMap a = Q.zeroMomentum := by
  rfl

/--
Weyl-reduction carrier data for measure/integral descent from a group to a torus.

This structure stores the root data and a Jacobian-type root weight map that is
used as the reduction factor in Weyl-style formulas.
-/
structure WeylIntegrationData (GaugeGroup Torus : Type) where
  /-- Weyl group controlling residual symmetries. -/
  weylGroup : Type*
  /-- Positive root labels appearing in the Jacobian factor. -/
  positiveRoots : Type*
  /-- A root-valued weight used as a Jacobian ingredient (e.g. Vandermonde). -/
  rootWeight : positiveRoots → ℝ
  /-- A distinguished torus reduction map from the original group. -/
  torusMap : GaugeGroup → Torus
  /-- Total root-weight product; the structural shadow of the denominator factor. -/
  rootMeasureProduct : ℝ := 0
  /-- Numerical shadow of the reduced volume/integral. -/
  volumeShadow : ℝ

/--
Pullback along the torus map.
-/
def WeylIntegrationData.pullback
    {GaugeGroup Torus : Type} (W : WeylIntegrationData GaugeGroup Torus)
    (f : Torus → ℝ) : GaugeGroup → ℝ :=
  fun g => f (W.torusMap g)

/--
Closed local theorem: Weyl pullback evaluates by applying the function after
the torus reduction map.
-/
theorem WeylIntegrationData.pullback_apply
    {GaugeGroup Torus : Type} (W : WeylIntegrationData GaugeGroup Torus)
    (f : Torus → ℝ) (g : GaugeGroup) :
    W.pullback f g = f (W.torusMap g) := by
  rfl

/--
Combined carrier data for Atiyah--Bott/Abelian-reduction style localization.

The combined carrier is an owner-level shape: the moduli object is presented with
its momentum constraint and a Weyl-type torus reduction shadow.
-/
structure SymplecticWeylVolumeData (Space GaugeGroup Torus : Type) [instGroup : Group GaugeGroup] where
  /-- Symplectic quotient layer. -/
  quotient : SymplecticQuotientData Space GaugeGroup
  /-- Weyl torus-reduction layer. -/
  weyl : WeylIntegrationData GaugeGroup Torus

/--
Canonical assembly from separate symplectic-quotient and Weyl-reduction data.
-/
def constructSymplecticWeylVolumeData
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    SymplecticWeylVolumeData.{0, 0, 0, 0, 0} Space GaugeGroup Torus :=
  ⟨Q, W⟩

/--
Closed local theorem: the assembled carrier has the supplied quotient data.
-/
theorem constructSymplecticWeylVolumeData_quotient
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).quotient = Q := by
  rfl

/--
Closed local theorem: the assembled carrier has the supplied Weyl data.
-/
theorem constructSymplecticWeylVolumeData_weyl
    {Space GaugeGroup Torus : Type} [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData.{0, 0, 0} Space GaugeGroup)
    (W : WeylIntegrationData.{0, 0} GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).weyl = W := by
  rfl

/--
Connector data for the theorem-safe Weyl-integration scaffold.

This does not prove the Weyl integration formula.  It records the existing
owner surfaces that such a formula must pass through: torus pullback, coadjoint
orbit, finite Mellin scaling, finite spectral Taylor/Mellin readout, and the
scale/shape channel split.
-/
structure WeylIntegrationPillarData
    (Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type)
    [Group GaugeGroup] [AddCommMonoid Func] [CommSemiring R] [Fintype ι] where
  /-- Gauge-theoretic symplectic quotient carrier. -/
  quotient : SymplecticQuotientData Space GaugeGroup
  /-- Weyl torus-reduction carrier. -/
  weyl : WeylIntegrationData GaugeGroup Torus
  /-- Coadjoint orbit/metriplectic carrier from the Souriau owner. -/
  orbit : InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg
  /-- Finite Mellin orbit-scaling datum. -/
  mellin : FiniteMellinScalingDatum Func R
  /-- Finite spectral Taylor/Mellin packet. -/
  spectral : SpectralTaylorMellinPacket ι
  /-- Analytic scale/shape channel split. -/
  scaleShape : LaplaceMellinScaleShapePacket

namespace WeylIntegrationPillarData

variable {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
variable [Group GaugeGroup] [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
variable (P : WeylIntegrationPillarData Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι)

/-- The connector still assembles the original symplectic/Weyl carrier. -/
def toSymplecticWeylVolumeData :
    SymplecticWeylVolumeData Space GaugeGroup Torus :=
  constructSymplecticWeylVolumeData P.quotient P.weyl

/-- Torus pullback is still owned by `WeylIntegrationData.pullback_apply`. -/
theorem torus_pullback_apply (f : Torus → ℝ) (g : GaugeGroup) :
    P.weyl.pullback f g = f (P.weyl.torusMap g) :=
  P.weyl.pullback_apply f g

/-- Coadjoint-orbit membership is delegated to the Souriau orbit owner. -/
theorem moment_mem_coadjoint_orbit (x : Orbit) :
    P.orbit.isOnCoadjointOrbit (P.orbit.moment x) :=
  InfiniteCoadjointOrbitMetriplecticContext.moment_lands_on_coadjoint_orbit P.orbit x

/-- Metriplectic nonnegativity is delegated to the coadjoint-orbit owner. -/
theorem totalEntropyRate_nonnegative (x : Orbit) :
    0 ≤ P.orbit.totalEntropyRate x :=
  InfiniteCoadjointOrbitMetriplecticContext.coadjoint_orbit_metriplectic_second_law
    P.orbit x

/-- Finite root/orbit Mellin character factorization is delegated to the Mellin owner. -/
theorem finite_mellin_orbit_factor (A : Finset ℕ) (f : Func) :
    P.mellin.Mellin (Finset.sum A (fun n => P.mellin.sample n f)) =
      finiteDirichletWeightSum A P.mellin.weight * P.mellin.Mellin f :=
  finite_sample_sum_factor_as_dirichlet_weight P.mellin A f

/--
Finite multiplicative orbit-character factorization is delegated to the Mellin
owner. This is the product-form corridor for Weyl-denominator root factors.
-/
theorem finite_mellin_orbit_product_factor (A : Finset ℕ) (f : Func) :
    (∏ n ∈ A, P.mellin.Mellin (P.mellin.sample n f)) =
      (∏ n ∈ A, P.mellin.weight n) * P.mellin.Mellin f ^ A.card := by
  calc
    (∏ n ∈ A, P.mellin.Mellin (P.mellin.sample n f))
        = ∏ n ∈ A, P.mellin.weight n * P.mellin.Mellin f := by
            refine Finset.prod_congr rfl ?_
            intro n hn
            rw [P.mellin.sample_law n f]
    _ = (∏ n ∈ A, P.mellin.weight n) *
          (∏ _n ∈ A, P.mellin.Mellin f) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ n ∈ A, P.mellin.weight n) * P.mellin.Mellin f ^ A.card := by
          simp

/-- Finite spectral heat readout uses the Taylor/Mellin owner. -/
theorem spectral_heat_readout_eq_prefix (t : ℂ) (N : ℕ) :
    InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatTaylorReadout P.spectral.data t N =
      InfoGeometry.Analysis.FiniteSpectralMellinTaylor.FiniteSpectralData.taylorMomentPrefix
        P.spectral.data
        (InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatTaylorCoeff t) N :=
  SpectralTaylorMellinPacket.heat_readout_eq_prefix P.spectral t N

/-- Finite spectral scalar readout uses the Taylor/Mellin owner. -/
theorem spectral_scalar_readout_eq :
    InfoGeometry.Analysis.FiniteSpectralHeatMellin.heatMellinReadout
        P.spectral.data P.spectral.heatMellinScalar =
      InfoGeometry.Analysis.FiniteSpectralHeatMellin.spectralScalingReadout
        P.spectral.data P.spectral.scaleScalar :=
  SpectralTaylorMellinPacket.scalar_readout_eq P.spectral

end WeylIntegrationPillarData

/-- The kernel lane used by the Weyl/Fourier side is exactly the Fourier-axis Laplace owner. -/
theorem weylKernel_laplaceTransform_eq_fourierChar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (w : ℝ) :
    InfoGeometry.Analysis.LaplaceTransform.laplaceTransform f
        ((2 * Real.pi * Complex.I) * w) =
      ∫ t : ℝ, (Real.fourierChar (-(w * t)) : ℂ) • f t :=
  InfoGeometry.Analysis.LaplaceFourierComparison.laplaceTransform_eq_fourierChar
    (f := f) (w := w)

/--
Algebraic two-channel shadow of a split boundary metric bracket.

The factors `gPlus` and `gMinus` are the dual metric coefficients after
restriction to the boundary; `left` and `right` are the already-evaluated
chiral operator/readout products.
-/
def splitBoundaryMetricBracket {R : Type*} [Semiring R]
    (gPlus gMinus left right : R) : R :=
  gPlus * left + gMinus * right

/--
If both boundary dual metric coefficients vanish, the split metric bracket
vanishes.  This is the kernel-checkable algebraic part of the proposed
metriplectic boundary barrier.
-/
theorem splitBoundaryMetricBracket_eq_zero_of_boundary_dual_zero
    {R : Type*} [Semiring R]
    {gPlus gMinus left right : R}
    (hgPlus : gPlus = 0) (hgMinus : gMinus = 0) :
    splitBoundaryMetricBracket gPlus gMinus left right = 0 := by
  simp [splitBoundaryMetricBracket, hgPlus, hgMinus]

/-- Coordinate-free algebraic Connes/Radon--Nikodym boundary velocity shadow. -/
def connesBoundaryCocycleDerivative
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H₁ H₂ : E) : E :=
  Complex.I • (H₂ - H₁)

/-- Equal Hamiltonian readouts give zero boundary cocycle derivative. -/
theorem connesBoundaryCocycleDerivative_eq_zero_of_eq
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {H₁ H₂ : E}
    (hH : H₁ = H₂) :
    connesBoundaryCocycleDerivative H₁ H₂ = 0 := by
  subst H₂
  simp [connesBoundaryCocycleDerivative]

/-- Minimal carrier for the Klein-bottle sheet flip used by non-orientable boundary maps. -/
structure KleinBottleSheet (Carrier : Type*) where
  carrier : Carrier
  isChiral : Bool

/-- Orientation-reversing sheet transition: it preserves the carrier and flips chirality. -/
def kleinSheetFlip {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    KleinBottleSheet Carrier where
  carrier := A.carrier
  isChiral := !A.isChiral

@[simp] theorem kleinSheetFlip_carrier {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    (kleinSheetFlip A).carrier = A.carrier :=
  rfl

@[simp] theorem kleinSheetFlip_isChiral {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    (kleinSheetFlip A).isChiral = !A.isChiral :=
  rfl

/-- The Klein sheet transition is a genuine `Z₂` involution. -/
@[simp] theorem kleinSheetFlip_involutive {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    kleinSheetFlip (kleinSheetFlip A) = A := by
  cases A
  simp [kleinSheetFlip]

/-- Inner derivation/commutator with the convention `δ_H(X) = XH - HX`. -/
def boundaryInnerDerivation {A : Type*} [NonUnitalNonAssocRing A] (H X : A) : A :=
  X * H - H * X

/-- If an observable commutes with the generator, its boundary inner derivation vanishes. -/
theorem boundaryInnerDerivation_eq_zero_of_commute
    {A : Type*} [NonUnitalNonAssocRing A]
    {H X : A}
    (hcomm : X * H = H * X) :
    boundaryInnerDerivation H X = 0 := by
  rw [boundaryInnerDerivation, hcomm]
  simp

/--
Algebraic core of the non-orientable Connes 2-cochain before applying a trace
functional.  This is only the raw alternating derivation product; cyclicity is
not asserted here.
-/
def connesKleinBottleCochainCore
    {A : Type*} [NonUnitalNonAssocRing A]
    (HL HR : A) (A₀ A₁ A₂ : KleinBottleSheet A) : A :=
  A₀.carrier *
    (boundaryInnerDerivation HL A₁.carrier * boundaryInnerDerivation HR A₂.carrier -
      boundaryInnerDerivation HR A₁.carrier * boundaryInnerDerivation HL A₂.carrier)

/-- If the first inserted observable is boundary-flat for both generators, the cochain core vanishes. -/
theorem connesKleinBottleCochainCore_eq_zero_of_first_boundary_flat
    {A : Type*} [NonUnitalNonAssocRing A]
    (HL HR : A) (A₀ A₁ A₂ : KleinBottleSheet A)
    (hL : boundaryInnerDerivation HL A₁.carrier = 0)
    (hR : boundaryInnerDerivation HR A₁.carrier = 0) :
    connesKleinBottleCochainCore HL HR A₀ A₁ A₂ = 0 := by
  simp [connesKleinBottleCochainCore, hL, hR]

end LanglandsGWBridge

end InfoGeometry

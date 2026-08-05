import Mathlib.Tactic
import InfoGeometry.Analysis.LaplaceFourierComparison
import InfoGeometry.Analysis.MellinZetaScaling
import InfoGeometry.Analysis.SpectralTaylorMellinBridge
import InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.OperatorAlgebra.CrossoverResidue
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Experimental.WeylIntegrationFormula

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
open InfoGeometry.OperatorAlgebra.CrossoverResidue

/--
Symplectic quotient carrier data for a gauge action.

The fields are intentionally structural:

* `symplecticForm` is the symplectic-geometry carrier;
* `momentumMap` plays the role of a conserved/constraint-valued map `μ`;
* `zeroMomentum` marks the reduction locus `μ = 0`;
* `moduliSpace` is the reduced moduli object exported as carrier data.
* `gaugeAction` is the group action by the provided `Group` parameter.
--/
structure SymplecticQuotientData (Space : Type)
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    (GaugeGroup : Type) [instGroup : Group GaugeGroup] where
  /-- The symplectic carrier is the existing Kähler-information form owner. -/
  symplecticForm : InfoGeometry.Canonical.KaehlerGeometry.SymplecticForm Space
  /-- The moment map takes values in the dual module of the configuration space. -/
  momentumMap : Space → Module.Dual ℝ Space
  /-- Group action on the configuration space by the provided `Group` parameter. -/
  gaugeAction : GaugeGroup → Space → Space
  /-- Identity law for the explicitly supplied gauge action. -/
  gaugeAction_one : ∀ x, gaugeAction 1 x = x
  /-- Composition law for the explicitly supplied gauge action. -/
  gaugeAction_mul : ∀ g h x, gaugeAction (g * h) x = gaugeAction g (gaugeAction h x)

namespace SymplecticQuotientData

variable {Space GaugeGroup : Type}
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [Group GaugeGroup]

/-- The momentum-value carrier is the dual module, not an untyped socket. -/
abbrev momentumValue (Q : SymplecticQuotientData Space GaugeGroup) :=
  Module.Dual ℝ Space

/-- The constrained configuration carrier used by symplectic reduction. -/
def zeroLocusCarrier (Q : SymplecticQuotientData Space GaugeGroup) :=
  {a : Space // Q.momentumMap a = 0}

/-- Two constrained points are equivalent when related by the supplied gauge action. -/
def orbitRel (Q : SymplecticQuotientData Space GaugeGroup)
    (a b : Q.zeroLocusCarrier) : Prop :=
  ∃ g : GaugeGroup, Q.gaugeAction g a.1 = b.1

theorem orbitRel_refl (Q : SymplecticQuotientData Space GaugeGroup)
    (a : Q.zeroLocusCarrier) : Q.orbitRel a a := by
  exact ⟨1, Q.gaugeAction_one a.1⟩

theorem orbitRel_symm (Q : SymplecticQuotientData Space GaugeGroup)
    {a b : Q.zeroLocusCarrier} (h : Q.orbitRel a b) : Q.orbitRel b a := by
  rcases h with ⟨g, hg⟩
  refine ⟨g⁻¹, ?_⟩
  rw [← hg, ← Q.gaugeAction_mul, inv_mul_cancel, Q.gaugeAction_one]

theorem orbitRel_trans (Q : SymplecticQuotientData Space GaugeGroup)
    {a b c : Q.zeroLocusCarrier} (hab : Q.orbitRel a b) (hbc : Q.orbitRel b c) :
    Q.orbitRel a c := by
  rcases hab with ⟨g, hg⟩
  rcases hbc with ⟨h, hh⟩
  refine ⟨h * g, ?_⟩
  rw [Q.gaugeAction_mul, hg, hh]

def orbitSetoid (Q : SymplecticQuotientData Space GaugeGroup) :
    Setoid Q.zeroLocusCarrier where
  r := Q.orbitRel
  iseqv := {
    refl := Q.orbitRel_refl
    symm := Q.orbitRel_symm
    trans := Q.orbitRel_trans }

instance (Q : SymplecticQuotientData Space GaugeGroup) :
    Setoid Q.zeroLocusCarrier := Q.orbitSetoid

/-- The reduced moduli carrier is the orbit quotient of the zero-momentum locus. -/
abbrev moduliSpace (Q : SymplecticQuotientData Space GaugeGroup) :=
  Quotient Q.orbitSetoid

/-- Canonical projection to the reduced moduli carrier. -/
def moduliProjection (Q : SymplecticQuotientData Space GaugeGroup) :
    Q.zeroLocusCarrier → Q.moduliSpace :=
  Quotient.mk Q.orbitSetoid

end SymplecticQuotientData

/--
Fixed-point locus `μ⁻¹(0)` for the momentum map.
-/
def SymplecticQuotientData.zeroLocus
    {Space GaugeGroup : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData Space GaugeGroup) : Set Space :=
  {a : Space | Q.momentumMap a = 0}

/--
Closed local theorem: zero-locus membership is exactly the momentum-map equation.
-/
theorem SymplecticQuotientData.mem_zeroLocus_iff
    {Space GaugeGroup : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [instGroup : Group GaugeGroup]
    (Q : SymplecticQuotientData Space GaugeGroup) (a : Space) :
    a ∈ Q.zeroLocus ↔ Q.momentumMap a = 0 := by
  rfl

/-- Weyl reduction data is a native product of the root owner and torus map.

No additional compatibility law is carried here; those laws belong to the
underlying `WeylData` owner or to downstream integration theorems.
-/
abbrev WeylIntegrationData (GaugeGroup Torus : Type)
    [Group GaugeGroup] [Group Torus] :=
  WeylIntegration.WeylData GaugeGroup Torus × (GaugeGroup → Torus)

abbrev WeylIntegrationData.rootData
    {GaugeGroup Torus : Type} [Group GaugeGroup] [Group Torus]
    (W : WeylIntegrationData GaugeGroup Torus) :
    WeylIntegration.WeylData GaugeGroup Torus := W.1

abbrev WeylIntegrationData.torusMap
    {GaugeGroup Torus : Type} [Group GaugeGroup] [Group Torus]
    (W : WeylIntegrationData GaugeGroup Torus) : GaugeGroup → Torus := W.2

def WeylIntegrationData.mk
    {GaugeGroup Torus : Type} [Group GaugeGroup] [Group Torus]
    (rootData : WeylIntegration.WeylData GaugeGroup Torus)
    (torusMap : GaugeGroup → Torus) :
    WeylIntegrationData GaugeGroup Torus := (rootData, torusMap)

/--
Pullback along the torus map.
-/
def WeylIntegrationData.pullback
    {GaugeGroup Torus : Type} [Group GaugeGroup] [Group Torus]
    (W : WeylIntegrationData GaugeGroup Torus)
    (f : Torus → ℝ) : GaugeGroup → ℝ :=
  fun g => f (W.torusMap g)

/--
Closed local theorem: Weyl pullback evaluates by applying the function after
the torus reduction map.
-/
theorem WeylIntegrationData.pullback_apply
    {GaugeGroup Torus : Type} [Group GaugeGroup] [Group Torus]
    (W : WeylIntegrationData GaugeGroup Torus)
    (f : Torus → ℝ) (g : GaugeGroup) :
    W.pullback f g = f (W.torusMap g) := by
  rfl

/-! Combined carrier data has no additional law beyond its two components. -/
abbrev SymplecticWeylVolumeData (Space GaugeGroup Torus : Type)
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [instGroup : Group GaugeGroup] [Group Torus] :=
  SymplecticQuotientData Space GaugeGroup × WeylIntegrationData GaugeGroup Torus

abbrev SymplecticWeylVolumeData.quotient
    {Space GaugeGroup Torus : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [Group GaugeGroup] [Group Torus]
    (D : SymplecticWeylVolumeData Space GaugeGroup Torus) :
    SymplecticQuotientData Space GaugeGroup := D.1

abbrev SymplecticWeylVolumeData.weyl
    {Space GaugeGroup Torus : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [Group GaugeGroup] [Group Torus]
    (D : SymplecticWeylVolumeData Space GaugeGroup Torus) :
    WeylIntegrationData GaugeGroup Torus := D.2

/--
Canonical assembly from separate symplectic-quotient and Weyl-reduction data.
-/
def constructSymplecticWeylVolumeData
    {Space GaugeGroup Torus : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [instGroup : Group GaugeGroup] [Group Torus]
    (Q : SymplecticQuotientData Space GaugeGroup)
    (W : WeylIntegrationData GaugeGroup Torus) :
    SymplecticWeylVolumeData Space GaugeGroup Torus :=
  ⟨Q, W⟩

/--
Closed local theorem: the assembled carrier has the supplied quotient data.
-/
theorem constructSymplecticWeylVolumeData_quotient
    {Space GaugeGroup Torus : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [instGroup : Group GaugeGroup] [Group Torus]
    (Q : SymplecticQuotientData Space GaugeGroup)
    (W : WeylIntegrationData GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).quotient = Q := by
  rfl

/--
Closed local theorem: the assembled carrier has the supplied Weyl data.
-/
theorem constructSymplecticWeylVolumeData_weyl
    {Space GaugeGroup Torus : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [instGroup : Group GaugeGroup] [Group Torus]
    (Q : SymplecticQuotientData Space GaugeGroup)
    (W : WeylIntegrationData GaugeGroup Torus) :
    (constructSymplecticWeylVolumeData Q W).weyl = W := by
  rfl

/-! The pillar is a product of existing owner carriers, with no extra law. -/
abbrev WeylIntegrationPillarData
    (Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type)
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [Group GaugeGroup] [Group Torus] [AddCommMonoid Func] [CommSemiring R] [Fintype ι] :=
  SymplecticQuotientData Space GaugeGroup ×
    (WeylIntegrationData GaugeGroup Torus ×
      (InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg ×
        (FiniteMellinScalingDatum Func R ×
          (SpectralTaylorMellinPacket ι × LaplaceMellinScaleShapePacket))))

abbrev WeylIntegrationPillarData.quotient
    {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [Group GaugeGroup] [Group Torus] [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
    (P : WeylIntegrationPillarData Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι) := P.1

abbrev WeylIntegrationPillarData.weyl
    {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [Group GaugeGroup] [Group Torus] [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
    (P : WeylIntegrationPillarData Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι) := P.2.1

abbrev WeylIntegrationPillarData.orbit
    {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [Group GaugeGroup] [Group Torus] [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
    (P : WeylIntegrationPillarData Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι) := P.2.2.1

abbrev WeylIntegrationPillarData.mellin
    {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [Group GaugeGroup] [Group Torus] [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
    (P : WeylIntegrationPillarData Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι) := P.2.2.2.1

abbrev WeylIntegrationPillarData.spectral
    {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space] [Group GaugeGroup] [Group Torus]
    [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
    (P : WeylIntegrationPillarData Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι) := P.2.2.2.2.1

abbrev WeylIntegrationPillarData.scaleShape
    {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
    [NormedAddCommGroup Space] [InnerProductSpace ℝ Space] [Group GaugeGroup] [Group Torus]
    [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
    (P : WeylIntegrationPillarData Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι) := P.2.2.2.2.2

namespace WeylIntegrationPillarData

variable {Space GaugeGroup Torus Orbit LieAlg LieCoalg Func R ι : Type}
variable [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [Group GaugeGroup] [Group Torus] [AddCommMonoid Func] [CommSemiring R] [Fintype ι]
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
            rw [P.mellin.Mellin_sample_eq_weight_mul n f]
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
abbrev KleinBottleSheet (Carrier : Type*) := Carrier × Chirality

namespace KleinBottleSheet

abbrev carrier {Carrier : Type*} (A : KleinBottleSheet Carrier) : Carrier := A.1

abbrev chirality {Carrier : Type*} (A : KleinBottleSheet Carrier) : Chirality := A.2

end KleinBottleSheet

/-- Orientation-reversing sheet transition: it preserves the carrier and flips chirality. -/
def kleinSheetFlip {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    KleinBottleSheet Carrier := (A.carrier, A.chirality.flip)

@[simp] theorem kleinSheetFlip_carrier {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    (kleinSheetFlip A).carrier = A.carrier :=
  rfl

@[simp] theorem kleinSheetFlip_chirality {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    (kleinSheetFlip A).chirality = A.chirality.flip :=
  rfl

/-- The Klein sheet transition is a genuine `Z₂` involution. -/
@[simp] theorem kleinSheetFlip_involutive {Carrier : Type*} (A : KleinBottleSheet Carrier) :
    kleinSheetFlip (kleinSheetFlip A) = A := by
  rcases A with ⟨carrier, chirality⟩
  change (carrier, chirality.flip.flip) = (carrier, chirality)
  simp

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

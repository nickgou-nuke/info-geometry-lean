import InfoGeometry.Twistor.Cl55CelestialOrderedExchangeRegularBraidMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Common-source intertwiner for celestial and boundary braid actions

The free regular module on the native presented braid group `B3` maps in two
directions:

* through the supplied celestial exchange-class homomorphism to the free
  module on the actual celestial fundamental group;
* through orbit evaluation to the native eight-dimensional boundary braid
  carrier.

Both maps are proved `B3`-equivariant.  This is a concrete common-source
comparison between geometric exchange classes and the native boundary/Yang--
Baxter representation.  It does not construct a map from the whole celestial
fundamental group to the boundary carrier or assert that the two target
representations are equivalent.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialBoundaryBraidRegularIntertwiner

open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Twistor.Cl55CelestialFundamentalGroupRegularMonodromy
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeRegularBraidMonodromy
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularMonodromy

variable
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma0 sigma1 : Equiv.Perm (Fin n))
    (gamma0 : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma0 p))
    (gamma1 : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma1 p))
    (hArtin :
      celestialOrderedExchangeLoopClass n p sigma0 gamma0 *
          celestialOrderedExchangeLoopClass n p sigma1 gamma1 *
          celestialOrderedExchangeLoopClass n p sigma0 gamma0 =
        celestialOrderedExchangeLoopClass n p sigma1 gamma1 *
          celestialOrderedExchangeLoopClass n p sigma0 gamma0 *
          celestialOrderedExchangeLoopClass n p sigma1 gamma1)

/-- The free complex module on the native presented braid group. -/
abbrev BoundaryBraidRegularModule :=
  GroupRegularModule ℂ BoundaryBraidGroup

/-- Linearization of the supplied celestial exchange-class homomorphism. -/
def celestialExchangeClassLinearMap :
    BoundaryBraidRegularModule →ₗ[ℂ]
      CelestialFundamentalGroupRegularModule ℂ n p :=
  groupHomRegularLinearMap ℂ BoundaryBraidGroup _
    (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin)

@[simp] theorem celestialExchangeClassLinearMap_single
    (g : BoundaryBraidGroup) (c : ℂ) :
    celestialExchangeClassLinearMap n p sigma0 sigma1 gamma0 gamma1 hArtin
        (Finsupp.single g c) =
      Finsupp.single
        (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin g) c := by
  exact groupHomRegularLinearMap_single ℂ BoundaryBraidGroup _ _ g c

/-- The exchange-class linearization intertwines regular `B3` action with the
geometric regular braid monodromy on actual loop classes. -/
theorem celestialExchangeClassLinearMap_intertwines
    (g : BoundaryBraidGroup) (x : BoundaryBraidRegularModule) :
    celestialExchangeClassLinearMap n p sigma0 sigma1 gamma0 gamma1 hArtin
        ((groupRegularLinearRepresentation ℂ BoundaryBraidGroup g :
          BoundaryBraidRegularModule →ₗ[ℂ] BoundaryBraidRegularModule) x) =
      (celestialExchangeRegularBraidMonodromy (R := ℂ) n p sigma0 sigma1
          gamma0 gamma1 hArtin g :
        CelestialFundamentalGroupRegularModule ℂ n p →ₗ[ℂ]
          CelestialFundamentalGroupRegularModule ℂ n p)
        (celestialExchangeClassLinearMap n p sigma0 sigma1
          gamma0 gamma1 hArtin x) := by
  exact groupHomRegularLinearMap_intertwines ℂ BoundaryBraidGroup _
    (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin) g x

/-- Orbit evaluation from the regular `B3` module into the native boundary
braid state space. -/
def boundaryBraidOrbitLinearMap (v : BoundaryBraidState) :
    BoundaryBraidRegularModule →ₗ[ℂ] BoundaryBraidState :=
  representationOrbitLinearMap ℂ BoundaryBraidGroup BoundaryBraidState
    boundaryBraidLinearRepresentation v

@[simp] theorem boundaryBraidOrbitLinearMap_single
    (v : BoundaryBraidState) (g : BoundaryBraidGroup) (c : ℂ) :
    boundaryBraidOrbitLinearMap v (Finsupp.single g c) =
      c • (boundaryBraidLinearRepresentation g :
        BoundaryBraidState →ₗ[ℂ] BoundaryBraidState) v := by
  exact representationOrbitLinearMap_single ℂ BoundaryBraidGroup
    BoundaryBraidState boundaryBraidLinearRepresentation v g c

/-- Orbit evaluation intertwines the regular action with the native boundary
braid/Yang--Baxter representation. -/
theorem boundaryBraidOrbitLinearMap_intertwines
    (v : BoundaryBraidState) (g : BoundaryBraidGroup)
    (x : BoundaryBraidRegularModule) :
    boundaryBraidOrbitLinearMap v
        ((groupRegularLinearRepresentation ℂ BoundaryBraidGroup g :
          BoundaryBraidRegularModule →ₗ[ℂ] BoundaryBraidRegularModule) x) =
      (boundaryBraidLinearRepresentation g :
        BoundaryBraidState →ₗ[ℂ] BoundaryBraidState)
        (boundaryBraidOrbitLinearMap v x) := by
  exact representationOrbitLinearMap_intertwines ℂ BoundaryBraidGroup
    BoundaryBraidState boundaryBraidLinearRepresentation v g x

/-- The two concrete target readouts form a single linear map from the common
regular `B3` source. -/
def celestialBoundaryBraidComparisonLinearMap (v : BoundaryBraidState) :
    BoundaryBraidRegularModule →ₗ[ℂ]
      (CelestialFundamentalGroupRegularModule ℂ n p × BoundaryBraidState) :=
  (celestialExchangeClassLinearMap n p sigma0 sigma1 gamma0 gamma1 hArtin).prod
    (boundaryBraidOrbitLinearMap v)

/-- The common-source comparison map is equivariant componentwise under the
geometric and native boundary braid actions. -/
theorem celestialBoundaryBraidComparisonLinearMap_intertwines
    (v : BoundaryBraidState) (g : BoundaryBraidGroup)
    (x : BoundaryBraidRegularModule) :
    celestialBoundaryBraidComparisonLinearMap n p sigma0 sigma1 gamma0 gamma1
        hArtin v
        ((groupRegularLinearRepresentation ℂ BoundaryBraidGroup g :
          BoundaryBraidRegularModule →ₗ[ℂ] BoundaryBraidRegularModule) x) =
      ((celestialExchangeRegularBraidMonodromy (R := ℂ) n p sigma0 sigma1
          gamma0 gamma1 hArtin g :
          CelestialFundamentalGroupRegularModule ℂ n p →ₗ[ℂ]
            CelestialFundamentalGroupRegularModule ℂ n p)
          (celestialExchangeClassLinearMap n p sigma0 sigma1
            gamma0 gamma1 hArtin x),
        (boundaryBraidLinearRepresentation g :
          BoundaryBraidState →ₗ[ℂ] BoundaryBraidState)
          (boundaryBraidOrbitLinearMap v x)) := by
  apply Prod.ext
  · exact celestialExchangeClassLinearMap_intertwines
      n p sigma0 sigma1 gamma0 gamma1 hArtin g x
  · exact boundaryBraidOrbitLinearMap_intertwines v g x

/-- The first Artin basis generator is read simultaneously as its actual
celestial loop class and its native boundary/Yang--Baxter operator applied to
the chosen state. -/
@[simp] theorem celestialBoundaryBraidComparisonLinearMap_sig0
    (v : BoundaryBraidState) :
    celestialBoundaryBraidComparisonLinearMap n p sigma0 sigma1 gamma0 gamma1
        hArtin v
        (Finsupp.single
          (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) (1 : ℂ)) =
      (Finsupp.single
          (celestialOrderedExchangeLoopClass n p sigma0 gamma0) (1 : ℂ),
        (boundaryBraidLinearRepresentation
          (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) :
          BoundaryBraidState →ₗ[ℂ] BoundaryBraidState) v) := by
  simp [celestialBoundaryBraidComparisonLinearMap,
    celestialExchangeClassLinearMap_single,
    boundaryBraidOrbitLinearMap_single]

/-- The second Artin basis generator has the analogous simultaneous
geometric and native boundary readout. -/
@[simp] theorem celestialBoundaryBraidComparisonLinearMap_sig1
    (v : BoundaryBraidState) :
    celestialBoundaryBraidComparisonLinearMap n p sigma0 sigma1 gamma0 gamma1
        hArtin v
        (Finsupp.single
          (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) (1 : ℂ)) =
      (Finsupp.single
          (celestialOrderedExchangeLoopClass n p sigma1 gamma1) (1 : ℂ),
        (boundaryBraidLinearRepresentation
          (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) :
          BoundaryBraidState →ₗ[ℂ] BoundaryBraidState) v) := by
  simp [celestialBoundaryBraidComparisonLinearMap,
    celestialExchangeClassLinearMap_single,
    boundaryBraidOrbitLinearMap_single]

/-! ## Native boundary representation on the geometric exchange subgroup -/

/-- The subgroup of the celestial fundamental group actually generated as
the range of the supplied geometric `B3` realization. -/
abbrev CelestialExchangeSubgroup :=
  (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin).range

/-- Provided the native boundary representation kills every braid word whose
geometric exchange class is trivial, it descends to a genuine representation
of the geometric exchange subgroup of the celestial fundamental group. -/
def celestialExchangeSubgroupBoundaryRepresentation
    (hker :
      (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin).ker ≤
        boundaryBraidLinearRepresentation.ker) :
    CelestialExchangeSubgroup n p sigma0 sigma1 gamma0 gamma1 hArtin →*
      BoundaryBraidLinearCarrier :=
  representationOnHomRange BoundaryBraidGroup _ BoundaryBraidLinearCarrier
    (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin)
    boundaryBraidLinearRepresentation hker

/-- On every braid word, the descended geometric-subgroup representation is
exactly the native boundary/Yang--Baxter representation. -/
@[simp] theorem celestialExchangeSubgroupBoundaryRepresentation_rangeRestrict
    (hker :
      (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin).ker ≤
        boundaryBraidLinearRepresentation.ker)
    (g : BoundaryBraidGroup) :
    celestialExchangeSubgroupBoundaryRepresentation n p sigma0 sigma1
        gamma0 gamma1 hArtin hker
        (MonoidHom.rangeRestrict
          (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin) g) =
      boundaryBraidLinearRepresentation g := by
  exact representationOnHomRange_rangeRestrict BoundaryBraidGroup _
    BoundaryBraidLinearCarrier
    (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin)
    boundaryBraidLinearRepresentation hker g

/-- The kernel condition is not merely sufficient: it is exactly equivalent
to existence of a native boundary representation on the geometric exchange
subgroup whose pullback is the given `B3` representation. -/
theorem exists_celestialExchangeSubgroupBoundaryRepresentation_iff :
    (∃ rhoExchange :
        CelestialExchangeSubgroup n p sigma0 sigma1 gamma0 gamma1 hArtin →*
          BoundaryBraidLinearCarrier,
      rhoExchange.comp
          (MonoidHom.rangeRestrict
            (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin)) =
        boundaryBraidLinearRepresentation) ↔
      (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin).ker ≤
        boundaryBraidLinearRepresentation.ker := by
  exact exists_representationOnHomRange_iff BoundaryBraidGroup _
    BoundaryBraidLinearCarrier
    (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin)
    boundaryBraidLinearRepresentation

end InfoGeometry.Twistor.Cl55CelestialBoundaryBraidRegularIntertwiner

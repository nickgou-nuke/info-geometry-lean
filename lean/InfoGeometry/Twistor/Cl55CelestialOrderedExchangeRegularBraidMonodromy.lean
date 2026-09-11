import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55CelestialFundamentalGroupRegularMonodromy

/-!
# A regular B3 monodromy from supplied celestial exchange paths

Two supplied ordered celestial exchange paths descend to based loop classes in
the unordered configuration space.  If those two classes satisfy the adjacent
Artin relation, the native presented-group API gives a genuine `B3` map into
the actual fundamental group.  Composing with faithful regular monodromy gives
a literal linear `B3` representation on the free module of based loop classes.

The paths and their Artin homotopy-class relation are explicit inputs.  This
owner does not select canonical exchanges or identify the resulting regular
representation with Jones, Yang--Baxter, conformal-block, or anyon data.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialOrderedExchangeRegularBraidMonodromy

open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Twistor.Cl55CelestialFundamentalGroupRegularMonodromy
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration

variable {R : Type*} [Semiring R]

/-- The geometric `B3` realization determined by two supplied celestial
exchange classes satisfying the Artin relation. -/
def celestialExchangeClassMap
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
          celestialOrderedExchangeLoopClass n p sigma1 gamma1) :
    BoundaryBraidGroup →*
      @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) (Quotient.mk' p) :=
  homOfArtinPair
    (celestialOrderedExchangeLoopClass n p sigma0 gamma0)
    (celestialOrderedExchangeLoopClass n p sigma1 gamma1) hArtin

@[simp] theorem celestialExchangeClassMap_sig0
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
          celestialOrderedExchangeLoopClass n p sigma1 gamma1) :
    celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin
        (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) =
      celestialOrderedExchangeLoopClass n p sigma0 gamma0 := by
  exact homOfArtinPair_sig0 _ _ hArtin

@[simp] theorem celestialExchangeClassMap_sig1
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
          celestialOrderedExchangeLoopClass n p sigma1 gamma1) :
    celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin
        (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) =
      celestialOrderedExchangeLoopClass n p sigma1 gamma1 := by
  exact homOfArtinPair_sig1 _ _ hArtin

/-- The genuine regular linear `B3` representation associated to the two
supplied celestial exchange paths. -/
def celestialExchangeRegularBraidMonodromy
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
          celestialOrderedExchangeLoopClass n p sigma1 gamma1) :
    BoundaryBraidGroup →*
      LinearMap.GeneralLinearGroup R
        (CelestialFundamentalGroupRegularModule R n p) :=
  (celestialFundamentalGroupRegularMonodromy R n p).comp
    (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin)

@[simp] theorem celestialExchangeRegularBraidMonodromy_sig0_single
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
    (delta : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))
    (r : R) :
    (celestialExchangeRegularBraidMonodromy (R := R) n p sigma0 sigma1
        gamma0 gamma1 hArtin
        (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) :
      CelestialFundamentalGroupRegularModule R n p →ₗ[R]
        CelestialFundamentalGroupRegularModule R n p)
        (Finsupp.single delta r) =
      Finsupp.single
        (celestialOrderedExchangeLoopClass n p sigma0 gamma0 * delta) r := by
  rw [celestialExchangeRegularBraidMonodromy, MonoidHom.comp_apply,
    celestialExchangeClassMap_sig0]
  exact celestialFundamentalGroupRegularMonodromy_orderedExchange
    R n p sigma0 gamma0 delta r

@[simp] theorem celestialExchangeRegularBraidMonodromy_sig1_single
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
    (delta : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))
    (r : R) :
    (celestialExchangeRegularBraidMonodromy (R := R) n p sigma0 sigma1
        gamma0 gamma1 hArtin
        (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) :
      CelestialFundamentalGroupRegularModule R n p →ₗ[R]
        CelestialFundamentalGroupRegularModule R n p)
        (Finsupp.single delta r) =
      Finsupp.single
        (celestialOrderedExchangeLoopClass n p sigma1 gamma1 * delta) r := by
  rw [celestialExchangeRegularBraidMonodromy, MonoidHom.comp_apply,
    celestialExchangeClassMap_sig1]
  exact celestialFundamentalGroupRegularMonodromy_orderedExchange
    R n p sigma1 gamma1 delta r

end InfoGeometry.Twistor.Cl55CelestialOrderedExchangeRegularBraidMonodromy

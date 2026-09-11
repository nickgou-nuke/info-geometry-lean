import InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy

/-!
# Celestial pullback of projective-null local-system monodromy

The concrete continuous embedding of unordered celestial configurations into
unordered projective `Q55`-null configurations already induces a functor of
fundamental groupoids.  This owner precomposes an existing `ModuleCat`-valued
projective-null local system with that functor and identifies the resulting
celestial monodromy with the ambient monodromy after the induced map of based
fundamental groups.

This is categorical pullback of an existing local system.  It does not assert
that a conformal-block local system has been constructed, select exchange
loops, identify a spherical braid group, or supply an anyon interpretation.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialLocalSystemMonodromy

open CategoryTheory
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup
open InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {R : Type*} [Ring R]

/-- A module-valued local system on the celestial unordered-configuration
space, using the exact quotient topology already owned by the celestial
configuration layer. -/
abbrev CelestialConfigurationLocalSystem (R : Type*) [Ring R] (n : ℕ) :=
  let _inst : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  FundamentalGroupoid (CelestialUnorderedConfiguration n) ⥤ ModuleCat R

/-- Pull back an ambient projective-`Q55` local system along the concrete
celestial fundamental-groupoid functor. -/
def celestialPullbackLocalSystem
    (n : ℕ) (L : ConfigurationLocalSystem R Q55 n) :
    CelestialConfigurationLocalSystem R n := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  exact celestialUnorderedFundamentalGroupoidMap n ⋙ L

/-- Monodromy of the celestial pullback local system at a chosen celestial
configuration. -/
def celestialPullbackMonodromy
    (n : ℕ) (L : ConfigurationLocalSystem R Q55 n)
    (p : CelestialUnorderedConfiguration n) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let _targetTopology : TopologicalSpace (Unordered Q55 n) :=
      unorderedConfigurationTopology Q55 n
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) p →*
      End ((celestialPullbackLocalSystem n L).obj
        (FundamentalGroupoid.mk p)) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  exact (celestialPullbackLocalSystem n L).mapEnd
    (FundamentalGroupoid.mk p)

/-- The celestial pullback monodromy is exactly the ambient local-system
monodromy evaluated after the induced celestial map of fundamental groups. -/
theorem celestialPullbackMonodromy_eq_ambient
    (n : ℕ) (L : ConfigurationLocalSystem R Q55 n)
    (p : CelestialUnorderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) p) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let _targetTopology : TopologicalSpace (Unordered Q55 n) :=
      unorderedConfigurationTopology Q55 n
    celestialPullbackMonodromy n L p gamma =
      localSystemMonodromy Q55 n L
        (celestialUnorderedConfigurationContinuousMap n p)
        (celestialUnorderedFundamentalGroupMap n p gamma) := by
  rfl

/-- The general-linear monodromy representation carried by the celestial
pullback local system. -/
def celestialPullbackLinearMonodromy
    (n : ℕ) (L : ConfigurationLocalSystem R Q55 n)
    (p : CelestialUnorderedConfiguration n) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let _targetTopology : TopologicalSpace (Unordered Q55 n) :=
      unorderedConfigurationTopology Q55 n
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) p →*
      LinearMap.GeneralLinearGroup R
        ((celestialPullbackLocalSystem n L).obj
          (FundamentalGroupoid.mk p)) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  exact ((moduleCatEndToLinearEnd
      ((celestialPullbackLocalSystem n L).obj (FundamentalGroupoid.mk p))).comp
    (celestialPullbackMonodromy n L p)).toHomUnits

/-- The celestial `GL`-valued monodromy is the ambient `GL`-valued monodromy
evaluated after the induced map of based fundamental groups. -/
theorem celestialPullbackLinearMonodromy_eq_ambient
    (n : ℕ) (L : ConfigurationLocalSystem R Q55 n)
    (p : CelestialUnorderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) p) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let _targetTopology : TopologicalSpace (Unordered Q55 n) :=
      unorderedConfigurationTopology Q55 n
    celestialPullbackLinearMonodromy n L p gamma =
      localSystemLinearMonodromy Q55 n L
        (celestialUnorderedConfigurationContinuousMap n p)
        (celestialUnorderedFundamentalGroupMap n p gamma) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  apply Units.ext
  apply LinearMap.ext
  intro x
  change (celestialPullbackMonodromy n L p gamma).hom x =
    (localSystemMonodromy Q55 n L
      (celestialUnorderedConfigurationContinuousMap n p)
      (celestialUnorderedFundamentalGroupMap n p gamma)).hom x
  rw [celestialPullbackMonodromy_eq_ambient]
  rfl

end InfoGeometry.Twistor.Cl55CelestialLocalSystemMonodromy

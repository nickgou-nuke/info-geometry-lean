import InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
import InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
import InfoGeometry.Twistor.ProjectiveNullConfigurationAssociatedDeckMonodromy
import Mathlib.GroupTheory.Perm.Sign

/-!
# Celestial deck-phase monodromy

The concrete celestial exchange class maps to the ambient `Q55` configuration
covering.  Composing ambient covering monodromy with a linear representation
of the deck group gives a literal celestial `pi_1` representation.  The sign
representation supplies a concrete scalar `±1` phase readout.

This phase factors through `S_n`; it therefore does not detect pure braids and
is not identified with Fibonacci, conformal-block, or general Yang--Baxter
monodromy.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialDeckPhaseMonodromy

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationAssociatedDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

section Associated

variable {R H : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

/-- Pull an associated ambient `Q55` deck representation back along the
celestial map on fundamental groups. -/
def celestialAssociatedDeckLinearMonodromy
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (rho : Equiv.Perm (Fin n) →*
      LinearMap.GeneralLinearGroup R H) :
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) (Quotient.mk' p) →*
      LinearMap.GeneralLinearGroup R H :=
  (associatedDeckLinearMonodromy Q55 n
    (q55OrderedConfiguration_locallyCompactSpace n)
    (q55OrderedConfiguration_t2Space n)
    (celestialOrderedConfigurationMap n p) rho).comp
      (celestialUnorderedFundamentalGroupMap n (Quotient.mk' p))

/-- A supplied celestial ordered exchange is read by the associated deck
representation at its endpoint permutation. -/
@[simp] theorem celestialAssociatedDeckLinearMonodromy_orderedExchange
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p))
    (rho : Equiv.Perm (Fin n) →*
      LinearMap.GeneralLinearGroup R H) :
    celestialAssociatedDeckLinearMonodromy n p rho
        (celestialOrderedExchangeLoopClass n p sigma gamma) = rho sigma := by
  unfold celestialAssociatedDeckLinearMonodromy
  rw [MonoidHom.comp_apply]
  have hmap :=
    celestialUnorderedFundamentalGroupMap_orderedExchangeLoopClass
      n p sigma gamma
  calc
    associatedDeckLinearMonodromy Q55 n
          (q55OrderedConfiguration_locallyCompactSpace n)
          (q55OrderedConfiguration_t2Space n)
          (celestialOrderedConfigurationMap n p) rho
          (celestialUnorderedFundamentalGroupMap n (Quotient.mk' p)
            (celestialOrderedExchangeLoopClass n p sigma gamma)) =
        associatedDeckLinearMonodromy Q55 n
          (q55OrderedConfiguration_locallyCompactSpace n)
          (q55OrderedConfiguration_t2Space n)
          (celestialOrderedConfigurationMap n p) rho
          (orderedExchangeLoopClass Q55 n
            (celestialOrderedConfigurationMap n p) sigma
            (celestialOrderedExchangeAmbientPath n p sigma gamma)) :=
      congrArg _ hmap
    _ = rho sigma :=
      associatedDeckLinearMonodromy_orderedExchangeLoopClass
        Q55 n (q55OrderedConfiguration_locallyCompactSpace n)
        (q55OrderedConfiguration_t2Space n)
        (celestialOrderedConfigurationMap n p) sigma
        (celestialOrderedExchangeAmbientPath n p sigma gamma) rho

end Associated

section SignPhase

variable {R H : Type*} (R H) [CommRing R] [AddCommGroup H] [Module R H]

/-- Scalar action of coefficient-ring units on an `R`-module, packaged as a
general-linear representation. -/
def unitScalarLinearRepresentation :
    Rˣ →* LinearMap.GeneralLinearGroup R H where
  toFun u := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (DistribMulAction.toLinearEquiv R H u)
  map_one' := by
    apply Units.ext
    ext x
    simp
  map_mul' u v := by
    apply Units.ext
    ext x
    dsimp [LinearMap.GeneralLinearGroup.ofLinearEquiv,
      DistribMulAction.toLinearEquiv, DistribMulAction.toAddEquiv,
      DistribSMul.toLinearMap]
    exact mul_smul u v x

/-- The sign character of `S_n`, cast into `R` and acting by scalar linear
automorphisms. -/
def deckSignLinearRepresentation (n : ℕ) :
    Equiv.Perm (Fin n) →* LinearMap.GeneralLinearGroup R H :=
  (unitScalarLinearRepresentation R H).comp
    ((Units.map (Int.castRingHom R).toMonoidHom).comp Equiv.Perm.sign)

@[simp] theorem deckSignLinearRepresentation_apply
    (n : ℕ) (sigma : Equiv.Perm (Fin n)) (x : H) :
    (deckSignLinearRepresentation R H n sigma : H →ₗ[R] H) x =
      (Equiv.Perm.sign sigma : R) • x := by
  rfl

/-- Concrete celestial sign-phase monodromy. -/
def celestialDeckSignMonodromy
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) (Quotient.mk' p) →*
      LinearMap.GeneralLinearGroup R H :=
  celestialAssociatedDeckLinearMonodromy n p
    (deckSignLinearRepresentation R H n)

/-- An explicit celestial exchange acts by its actual permutation sign on
every state in the coefficient module. -/
@[simp] theorem celestialDeckSignMonodromy_orderedExchange_apply
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) (x : H) :
    (celestialDeckSignMonodromy R H n p
        (celestialOrderedExchangeLoopClass n p sigma gamma) : H →ₗ[R] H) x =
      (Equiv.Perm.sign sigma : R) • x := by
  rw [celestialDeckSignMonodromy,
    celestialAssociatedDeckLinearMonodromy_orderedExchange,
    deckSignLinearRepresentation_apply]

end SignPhase

end InfoGeometry.Twistor.Cl55CelestialDeckPhaseMonodromy

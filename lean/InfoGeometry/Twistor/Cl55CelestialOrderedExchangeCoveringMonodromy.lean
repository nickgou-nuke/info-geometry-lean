import InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
import InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem
import InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy

/-!
# Celestial ordered exchanges in the `Q55` covering local system

The ordered-to-unordered `Q55` configuration covering already owns a concrete
free-module local system.  This file pulls that local system back to the
celestial configuration space and evaluates an explicit celestial ordered
exchange path on its canonical deck-label basis.  The result is left
multiplication by the endpoint permutation.

This is genuine covering-space monodromy of a supplied path.  It is not a
Yang--Baxter phase local system, a preferred braid generator, a spherical
braid-group identification, or an anyon theory.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialOrderedExchangeCoveringMonodromy

open CategoryTheory
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55CelestialLocalSystemMonodromy
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem
open InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv
open InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {R : Type*} [Ring R]

/-- The native ordered-to-unordered `Q55` covering local system. -/
def q55ConfigurationCoveringLocalSystem (R : Type*) [Ring R] (n : ℕ) :
    ConfigurationLocalSystem R Q55 n :=
  unorderedConfigurationCoveringLocalSystem (R := R) Q55 n
    (q55OrderedConfiguration_locallyCompactSpace n)
    (q55OrderedConfiguration_t2Space n)

/-- Pullback of the concrete `Q55` covering local system to celestial
unordered configurations. -/
def celestialQ55CoveringLocalSystem (R : Type*) [Ring R] (n : ℕ) :
    CelestialConfigurationLocalSystem R n :=
  celestialPullbackLocalSystem n (q55ConfigurationCoveringLocalSystem R n)

/-- An explicit celestial ordered exchange acts on the canonical covering
fiber basis by left multiplication with its endpoint permutation. -/
@[simp] theorem celestialQ55CoveringLinearMonodromy_orderedExchange_single
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma tau : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) (a : R) :
    let L := q55ConfigurationCoveringLocalSystem R n
    let ambientP := celestialOrderedConfigurationMap n p
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let _targetTopology : TopologicalSpace (Unordered Q55 n) :=
      unorderedConfigurationTopology Q55 n
    (celestialPullbackLinearMonodromy n L (Quotient.mk' p)
        (celestialOrderedExchangeLoopClass n p sigma gamma) :
      Module.End R
        ((celestialPullbackLocalSystem n L).obj
          (FundamentalGroupoid.mk (Quotient.mk' p))))
        (Finsupp.single (orderedFiberEquivPerm Q55 n ambientP tau) a) =
      Finsupp.single (orderedFiberEquivPerm Q55 n ambientP (sigma * tau)) a := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Ordered Q55 n) :=
    orderedConfigurationTopology Q55 n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  dsimp only
  rw [celestialPullbackLinearMonodromy_orderedExchangeLoopClass]
  unfold q55ConfigurationCoveringLocalSystem
  have h :=
    unorderedConfigurationCoveringLocalSystem_monodromy_label_single
      (R := R) Q55 n
      (q55OrderedConfiguration_locallyCompactSpace n)
      (q55OrderedConfiguration_t2Space n)
      (celestialOrderedConfigurationMap n p)
      (orderedExchangeLoopClass Q55 n
        (celestialOrderedConfigurationMap n p) sigma
        (celestialOrderedExchangeAmbientPath n p sigma gamma)) tau a
  simpa only [
    unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass] using h

end InfoGeometry.Twistor.Cl55CelestialOrderedExchangeCoveringMonodromy

import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration

/-!
# Fundamental-group transport from celestial to `Q55` null configurations

The continuous embedding of unordered celestial configurations into unordered
projective `Q55`-null configurations induces Mathlib's native map of
fundamental groupoids and, at every chosen basepoint, the corresponding
homomorphism of based fundamental groups.

The basepoint is sent to its image.  No injectivity or surjectivity statement
for the induced fundamental-group homomorphism, spherical-braid
identification, selected exchange loop, or anyon monodromy is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup

open CategoryTheory
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- The existing celestial unordered-configuration embedding, packaged as a
continuous map for the exact source and target quotient topologies. -/
def celestialUnorderedConfigurationContinuousMap (n : ℕ) :
    @ContinuousMap
      (CelestialUnorderedConfiguration n)
      (Unordered Q55 n)
      (celestialUnorderedConfigurationTopology n)
      (unorderedConfigurationTopology Q55 n) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  exact ⟨celestialUnorderedConfigurationMap n,
    celestialUnorderedConfigurationMap_continuous n⟩

@[simp] theorem celestialUnorderedConfigurationContinuousMap_apply
    (n : ℕ) (p : CelestialUnorderedConfiguration n) :
    celestialUnorderedConfigurationContinuousMap n p =
      celestialUnorderedConfigurationMap n p :=
  by simp [celestialUnorderedConfigurationContinuousMap]

/-- Functorial transport of paths and path-homotopy classes from the
celestial unordered configuration space into the ambient projective-null
configuration space. -/
def celestialUnorderedFundamentalGroupoidMap (n : ℕ) :
    let _ := celestialUnorderedConfigurationTopology n
    let _ := unorderedConfigurationTopology Q55 n
    FundamentalGroupoid (CelestialUnorderedConfiguration n) ⥤
      FundamentalGroupoid (Unordered Q55 n) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  exact FundamentalGroupoid.map
    (celestialUnorderedConfigurationContinuousMap n)

/-- The based fundamental-group homomorphism induced by the concrete
celestial unordered-configuration embedding.  Its target basepoint is the
image of the chosen celestial configuration. -/
def celestialUnorderedFundamentalGroupMap
    (n : ℕ) (p : CelestialUnorderedConfiguration n) :
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) p →*
      @FundamentalGroup
        (Unordered Q55 n)
        (unorderedConfigurationTopology Q55 n)
        (celestialUnorderedConfigurationContinuousMap n p) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  exact FundamentalGroup.map
    (celestialUnorderedConfigurationContinuousMap n) p

/-- Pointwise, the based homomorphism is exactly Mathlib's induced map for
the same continuous celestial embedding. -/
@[simp] theorem celestialUnorderedFundamentalGroupMap_apply
    (n : ℕ) (p : CelestialUnorderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) p) :
    celestialUnorderedFundamentalGroupMap n p gamma =
      @FundamentalGroup.map
        (CelestialUnorderedConfiguration n)
        (Unordered Q55 n)
        (celestialUnorderedConfigurationTopology n)
        (unorderedConfigurationTopology Q55 n)
        (celestialUnorderedConfigurationContinuousMap n) p gamma :=
  rfl

end InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup

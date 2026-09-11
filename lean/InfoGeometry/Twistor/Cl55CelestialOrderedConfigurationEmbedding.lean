import InfoGeometry.Twistor.Cl55MinkowskiCelestialSliceTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

/-!
# Celestial ordered configurations inside the projective `Q55` null boundary

The closed celestial embedding is lifted componentwise to finite ordered
configurations of distinct points.  This owner proves an embedding of concrete
celestial configurations into the existing projective-null configuration
carrier.  It does not identify the whole null boundary with a sphere and does
not interpret a configuration-space self-map as a braid path or monodromy.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSliceTopology
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

/-- Ordered configurations of distinct points on the concrete celestial
sphere. -/
abbrev CelestialOrderedConfiguration (n : ℕ) :=
  OrderedConfiguration CelestialSphere n

/-- The inherited topology from the finite function space of celestial
directions. -/
def celestialOrderedConfigurationTopology (n : ℕ) :
    TopologicalSpace (CelestialOrderedConfiguration n) :=
  TopologicalSpace.induced Subtype.val inferInstance

/-- Apply the celestial null embedding componentwise to an ordered distinct
configuration. -/
def celestialOrderedConfigurationMap (n : ℕ) :
    CelestialOrderedConfiguration n → NullOrderedConfiguration Q55 n := by
  intro p
  refine ⟨fun i => celestialNullPoint (p.1 i), ?_⟩
  intro i j hij heq
  exact p.2 i j hij (celestialNullPoint_injective heq)

@[simp] theorem celestialOrderedConfigurationMap_apply
    (n : ℕ) (p : CelestialOrderedConfiguration n) (i : Fin n) :
    (celestialOrderedConfigurationMap n p).1 i =
      celestialNullPoint (p.1 i) :=
  rfl

/-- The componentwise celestial map is injective on ordered
configurations. -/
theorem celestialOrderedConfigurationMap_injective (n : ℕ) :
    Function.Injective (celestialOrderedConfigurationMap n) := by
  intro p q hpq
  apply Subtype.ext
  funext i
  apply celestialNullPoint_injective
  exact congrFun (congrArg Subtype.val hpq) i

/-- The pointwise map on the ambient finite function spaces is a topological
embedding. -/
theorem celestialPiMap_isEmbedding (n : ℕ) :
    let _ := nullBoundaryTopology Q55
    Topology.IsEmbedding
      (Pi.map (fun _ : Fin n => celestialNullPoint)) := by
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  exact Topology.IsEmbedding.piMap fun _ => celestialNullPoint_isEmbedding

/-- The concrete celestial configuration carrier embeds topologically into
the native ordered projective-null configuration carrier. -/
theorem celestialOrderedConfigurationMap_isEmbedding (n : ℕ) :
    @Topology.IsEmbedding
      (CelestialOrderedConfiguration n)
      (NullOrderedConfiguration Q55 n)
      (celestialOrderedConfigurationTopology n)
      (orderedConfigurationTopology Q55 n)
      (celestialOrderedConfigurationMap n) := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (NullOrderedConfiguration Q55 n) :=
    orderedConfigurationTopology Q55 n
  have hpi : Topology.IsEmbedding
      (Pi.map (fun _ : Fin n => celestialNullPoint)) :=
    celestialPiMap_isEmbedding n
  have hsource : Topology.IsEmbedding
      (Subtype.val : CelestialOrderedConfiguration n →
        (Fin n → CelestialSphere)) :=
    Topology.IsEmbedding.subtypeVal
  have hcomp : Topology.IsEmbedding
      ((Pi.map (fun _ : Fin n => celestialNullPoint)) ∘
        (Subtype.val : CelestialOrderedConfiguration n →
          (Fin n → CelestialSphere))) :=
    hpi.comp hsource
  have htarget : Topology.IsEmbedding
      (Subtype.val : NullOrderedConfiguration Q55 n →
        (Fin n → TwistorSpace Q55)) :=
    Topology.IsEmbedding.subtypeVal
  apply htarget.of_comp_iff.mp
  change Topology.IsEmbedding
    ((Pi.map (fun _ : Fin n => celestialNullPoint)) ∘
      (Subtype.val : CelestialOrderedConfiguration n →
        (Fin n → CelestialSphere)))
  exact hcomp

/-- Hence the celestial configuration space is homeomorphic to its actual
range in the ordered projective-null configuration carrier. -/
noncomputable def celestialOrderedConfigurationRangeHomeomorph (n : ℕ) :
    let _ := orderedConfigurationTopology Q55 n
    let _ := celestialOrderedConfigurationTopology n
    CelestialOrderedConfiguration n ≃ₜ
      Set.range (celestialOrderedConfigurationMap n) := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (NullOrderedConfiguration Q55 n) :=
    orderedConfigurationTopology Q55 n
  exact (celestialOrderedConfigurationMap_isEmbedding n).toHomeomorph

end InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding

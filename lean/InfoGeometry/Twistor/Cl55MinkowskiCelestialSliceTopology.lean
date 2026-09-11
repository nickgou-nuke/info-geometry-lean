import InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55ProjectivizationTopology
import InfoGeometry.Twistor.ProjectiveNullBoundaryTopology
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Topology of the Lorentzian celestial slice

This owner equips the concrete celestial sphere equation from
`Cl55MinkowskiCelestialSlice` with its inherited Euclidean topology and proves
that its native map into the projective `Q55` null boundary is a topological
embedding.  The result is only a homeomorphism onto the map's range; no global
identification of the null boundary with `S²` or `ℂP¹` is asserted.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.Cl55MinkowskiCelestialSliceTopology

open BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.Cl55ProjectivizationTopology
open InfoGeometry.Twistor.ProjectiveNullBoundaryTopology
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

/-- The Euclidean sphere equation is a closed subset of the coordinate
carrier. -/
theorem celestialSphereLocus_isClosed :
    IsClosed {x : Fin 3 → ℝ | ∑ i : Fin 3, x i ^ 2 = 1} := by
  exact isClosed_singleton.preimage (by fun_prop)

/-- Every coordinate of a point on the celestial sphere has norm at most one,
so the equation locus is bounded. -/
theorem celestialSphereLocus_isBounded :
    Bornology.IsBounded {x : Fin 3 → ℝ | ∑ i : Fin 3, x i ^ 2 = 1} := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  intro x hx
  have hcoord : ∀ i : Fin 3, ‖x i‖ ≤ 1 := by
    intro i
    have hi : x i ^ 2 ≤ ∑ j : Fin 3, x j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j))
        (Finset.mem_univ i)
    have hi' : x i ^ 2 ≤ 1 := by
      calc
        x i ^ 2 ≤ ∑ j : Fin 3, x j ^ 2 := hi
        _ = 1 := hx
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (x i)]
  rw [Pi.norm_def]
  norm_cast
  exact Finset.sup_le fun i _ => hcoord i

/-- Compactness of the concrete celestial sphere follows directly from its
closed bounded Euclidean equation. -/
theorem celestialSphereLocus_isCompact :
    IsCompact {x : Fin 3 → ℝ | ∑ i : Fin 3, x i ^ 2 = 1} := by
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨celestialSphereLocus_isClosed, celestialSphereLocus_isBounded⟩

/-- The celestial sphere subtype is compact in its inherited topology. -/
theorem celestialSphere_compactSpace : CompactSpace CelestialSphere :=
  isCompact_iff_compactSpace.mp celestialSphereLocus_isCompact

/-- The normalized null representative varies continuously with the celestial
direction. -/
theorem celestialVector_continuous : Continuous celestialVector := by
  exact minkowskiSlice.continuous_of_finiteDimensional.comp
    (continuous_const.prodMk continuous_subtype_val)

/-- The celestial map is continuous for the repository quotient topology on
projectivization and the induced topology on the null boundary. -/
theorem celestialNullPoint_continuous :
    @Continuous CelestialSphere (TwistorSpace Q55) inferInstance
      (nullBoundaryTopology Q55) celestialNullPoint := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  let q : {v : V55 // v ≠ 0} → ℙ ℝ V55 :=
    @Quotient.mk' _ (projectivizationSetoid ℝ V55)
  let inc : CelestialSphere → {v : V55 // v ≠ 0} := fun x =>
    ⟨celestialVector x, celestialVector_ne_zero x⟩
  have hinc : Continuous inc :=
    celestialVector_continuous.subtype_mk _
  apply Continuous.subtype_mk
  change Continuous (q ∘ inc)
  exact continuous_coinduced_rng.comp hinc

/-- The normalized celestial slice is a closed topological embedding into the
native projective-null boundary. -/
theorem celestialNullPoint_isClosedEmbedding :
    @Topology.IsClosedEmbedding CelestialSphere (TwistorSpace Q55)
      inferInstance (nullBoundaryTopology Q55) celestialNullPoint := by
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  letI : CompactSpace CelestialSphere := celestialSphere_compactSpace
  letI : T2Space (TwistorSpace Q55) :=
    nullBoundary_t2Space Q55 q55Projectivization_t2Space
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    celestialNullPoint_continuous celestialNullPoint_injective
    celestialNullPoint_continuous.isClosedMap

/-- In particular, the celestial slice is a topological embedding. -/
theorem celestialNullPoint_isEmbedding :
    @Topology.IsEmbedding CelestialSphere (TwistorSpace Q55)
      inferInstance (nullBoundaryTopology Q55) celestialNullPoint := by
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  exact celestialNullPoint_isClosedEmbedding.isEmbedding

/-- The concrete celestial sphere is homeomorphic to its actual image in the
projective `Q55` null boundary. -/
noncomputable def celestialNullPointRangeHomeomorph :
    let _ := nullBoundaryTopology Q55
    CelestialSphere ≃ₜ Set.range celestialNullPoint := by
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  exact celestialNullPoint_isEmbedding.toHomeomorph

end InfoGeometry.Twistor.Cl55MinkowskiCelestialSliceTopology

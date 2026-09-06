import InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding

/-!
# Unordered celestial configurations in the projective `Q55` null boundary

The componentwise celestial embedding is equivariant for finite reindexing,
so it descends to the genuine orbit quotient of distinct celestial
configurations.  The descended map into the existing unordered projective-null
configuration carrier is injective and continuous for the quotient topologies.

This is a map of configuration carriers.  It is not a computation of a
fundamental group, a spherical-braid identification, or monodromy.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- Reindex a concrete celestial configuration by a finite permutation. -/
def celestialPermute (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : CelestialOrderedConfiguration n) :
    CelestialOrderedConfiguration n := by
  refine ⟨fun i => p.1 (σ i), ?_⟩
  intro i j hij heq
  exact p.2 (σ i) (σ j) (fun h => hij (σ.injective h)) heq

@[simp] theorem celestialPermute_apply (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (p : CelestialOrderedConfiguration n)
    (i : Fin n) :
    (celestialPermute n σ p).1 i = p.1 (σ i) :=
  rfl

/-- The ordered celestial embedding commutes exactly with reindexing. -/
theorem celestialOrderedConfigurationMap_respects_permute
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : CelestialOrderedConfiguration n) :
    celestialOrderedConfigurationMap n (celestialPermute n σ p) =
      permute Q55 n σ (celestialOrderedConfigurationMap n p) := by
  apply Subtype.ext
  funext i
  rfl

/-- Pull back the native projective-null orbit relation along the injective
celestial ordered-configuration embedding. -/
def celestialReindexSetoid (n : ℕ) :
    Setoid (CelestialOrderedConfiguration n) :=
  Setoid.comap (celestialOrderedConfigurationMap n)
    (reindexSetoid Q55 n)

/-- The pulled-back relation is precisely the expected finite permutation
orbit relation on celestial configurations. -/
theorem celestialReindexSetoid_iff (n : ℕ)
    (p q : CelestialOrderedConfiguration n) :
    (celestialReindexSetoid n).r p q ↔
      ∃ σ : Equiv.Perm (Fin n), q = celestialPermute n σ p := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    apply celestialOrderedConfigurationMap_injective n
    calc
      celestialOrderedConfigurationMap n q =
          permute Q55 n σ (celestialOrderedConfigurationMap n p) := hσ
      _ = celestialOrderedConfigurationMap n (celestialPermute n σ p) :=
        (celestialOrderedConfigurationMap_respects_permute n σ p).symm
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, celestialOrderedConfigurationMap_respects_permute n σ p⟩

/-- The unordered celestial configuration carrier is the finite reindexing
orbit quotient. -/
abbrev CelestialUnorderedConfiguration (n : ℕ) :=
  Quotient (celestialReindexSetoid n)

instance celestialReindexSetoidInstance (n : ℕ) :
    Setoid (CelestialOrderedConfiguration n) :=
  celestialReindexSetoid n

/-- Descend the ordered celestial embedding to unordered configurations. -/
def celestialUnorderedConfigurationMap (n : ℕ) :
    CelestialUnorderedConfiguration n → Unordered Q55 n :=
  Quotient.map (celestialOrderedConfigurationMap n) (by
    intro p q hpq
    exact hpq)

@[simp] theorem celestialUnorderedConfigurationMap_mk
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    celestialUnorderedConfigurationMap n (Quotient.mk' p) =
      Quotient.mk' (celestialOrderedConfigurationMap n p) :=
  rfl

/-- Because the source relation is the exact pullback of the target orbit
relation, the descended unordered map is injective. -/
theorem celestialUnorderedConfigurationMap_injective (n : ℕ) :
    Function.Injective (celestialUnorderedConfigurationMap n) := by
  intro p q hpq
  revert hpq
  refine Quotient.inductionOn₂ p q ?_
  intro p q hpq
  change Quotient.mk' (celestialOrderedConfigurationMap n p) =
    Quotient.mk' (celestialOrderedConfigurationMap n q) at hpq
  apply Quotient.sound
  have htarget : (reindexSetoid Q55 n).r
      (celestialOrderedConfigurationMap n p)
      (celestialOrderedConfigurationMap n q) :=
    Quotient.exact hpq
  exact htarget

/-- The celestial unordered quotient receives the quotient topology induced
by its ordered configuration carrier. -/
def celestialUnorderedConfigurationTopology (n : ℕ) :
    TopologicalSpace (CelestialUnorderedConfiguration n) :=
  TopologicalSpace.coinduced
    (@Quotient.mk' (CelestialOrderedConfiguration n)
      (celestialReindexSetoid n))
    (celestialOrderedConfigurationTopology n)

/-- The canonical projection from ordered to unordered celestial
configurations is continuous for the defining quotient topology. -/
theorem celestialUnorderedProjection_continuous (n : ℕ) :
    @Continuous
      (CelestialOrderedConfiguration n)
      (CelestialUnorderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      (celestialUnorderedConfigurationTopology n)
      (@Quotient.mk' (CelestialOrderedConfiguration n)
        (celestialReindexSetoid n)) := by
  exact continuous_coinduced_rng

/-- The descended celestial map is continuous for the canonical quotient
topologies. -/
theorem celestialUnorderedConfigurationMap_continuous (n : ℕ) :
    @Continuous
      (CelestialUnorderedConfiguration n)
      (Unordered Q55 n)
      (celestialUnorderedConfigurationTopology n)
      (unorderedConfigurationTopology Q55 n)
      (celestialUnorderedConfigurationMap n) := by
  letI : TopologicalSpace (ℙ ℝ V55) :=
    projectivizationQuotientTopology (K := ℝ) (V := V55)
  letI : TopologicalSpace (TwistorSpace Q55) := nullBoundaryTopology Q55
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (NullOrderedConfiguration Q55 n) :=
    orderedConfigurationTopology Q55 n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  apply (continuous_coinduced_dom).2
  change Continuous
    ((Quotient.mk' : NullOrderedConfiguration Q55 n → Unordered Q55 n) ∘
      celestialOrderedConfigurationMap n)
  exact continuous_quotient_mk'.comp
    (celestialOrderedConfigurationMap_isEmbedding n).continuous

/-- The ordered and unordered celestial embeddings form the expected
commuting quotient square. -/
theorem celestialUnorderedProjection_comp_orderedMap (n : ℕ) :
    celestialUnorderedConfigurationMap n ∘
        (@Quotient.mk' (CelestialOrderedConfiguration n)
          (celestialReindexSetoid n)) =
      (@Quotient.mk' (NullOrderedConfiguration Q55 n)
        (reindexSetoid Q55 n)) ∘
        celestialOrderedConfigurationMap n := by
  funext p
  rfl

end InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration

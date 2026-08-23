import InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
import InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup

/-!
# Normalized null paravectors and celestial boundary configurations

The repository already owns the hard configuration-space layer on the
celestial slice: ordered and unordered configurations, permutation
reindexing, topological embeddings, and the induced fundamental-group map
into projective `Q55` null configurations.

This owner supplies the missing adapter from normalized null paravectors
`p = (1,n)` to that existing celestial carrier.  It therefore avoids a second
parallel configuration API and proves that the geometric anyon-position
carrier is exactly the already formalized celestial configuration space.

No claim is made that a single four-vector is itself an anyon.  Braid/anyon
data arise from exchange paths of configurations of these boundary points.
-/

noncomputable section

namespace InfoGeometry.Twistor.TwistorAnyonBoundaryConfiguration

open BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- A normalized future projective representative of a null Minkowski ray:
`p = (1,n)` with `|n|² = 1`. -/
abbrev NormalizedNullParavector :=
  {p : Minkowski13 // p.1 = 1 ∧ IsNullParavector p}

/-- Extract the celestial direction from a normalized null paravector. -/
def normalizedNullParavectorToCelestial
    (p : NormalizedNullParavector) : CelestialSphere := by
  refine ⟨p.1.2, ?_⟩
  have hnull := p.2.2
  rw [IsNullParavector, minkowski13Norm, p.2.1] at hnull
  linarith

/-- Reconstruct the normalized null paravector `(1,n)` from a celestial
direction. -/
def celestialToNormalizedNullParavector
    (x : CelestialSphere) : NormalizedNullParavector := by
  refine ⟨(1, x.1), rfl, ?_⟩
  unfold IsNullParavector minkowski13Norm
  simp [x.2]

@[simp] theorem normalizedNullParavectorToCelestial_inverse
    (x : CelestialSphere) :
    normalizedNullParavectorToCelestial
      (celestialToNormalizedNullParavector x) = x := by
  apply Subtype.ext
  rfl

@[simp] theorem celestialToNormalizedNullParavector_inverse
    (p : NormalizedNullParavector) :
    celestialToNormalizedNullParavector
      (normalizedNullParavectorToCelestial p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact p.2.1.symm
  · rfl

/-- Normalized null paravectors are exactly the celestial sphere carrier. -/
noncomputable def normalizedNullParavectorEquivCelestial :
    NormalizedNullParavector ≃ CelestialSphere where
  toFun := normalizedNullParavectorToCelestial
  invFun := celestialToNormalizedNullParavector
  left_inv := celestialToNormalizedNullParavector_inverse
  right_inv := normalizedNullParavectorToCelestial_inverse

/-- Ordered configurations of distinct normalized null paravectors. -/
abbrev NormalizedParavectorOrderedConfiguration (n : ℕ) :=
  OrderedConfiguration NormalizedNullParavector n

/-- Transport an ordered normalized-paravector configuration to the existing
celestial ordered-configuration carrier. -/
def normalizedParavectorToCelestialOrdered (n : ℕ) :
    NormalizedParavectorOrderedConfiguration n →
      CelestialOrderedConfiguration n := by
  intro p
  refine ⟨fun i => normalizedNullParavectorEquivCelestial (p.1 i), ?_⟩
  intro i j hij heq
  apply p.2 i j hij
  exact normalizedNullParavectorEquivCelestial.injective heq

/-- Transport a celestial ordered configuration back to normalized null
paravectors. -/
def celestialToNormalizedParavectorOrdered (n : ℕ) :
    CelestialOrderedConfiguration n →
      NormalizedParavectorOrderedConfiguration n := by
  intro p
  refine ⟨fun i => normalizedNullParavectorEquivCelestial.symm (p.1 i), ?_⟩
  intro i j hij heq
  apply p.2 i j hij
  exact normalizedNullParavectorEquivCelestial.symm.injective heq

/-- The two ordered configuration carriers are genuinely equivalent, not
merely equinumerous. -/
noncomputable def normalizedParavectorOrderedEquivCelestial (n : ℕ) :
    NormalizedParavectorOrderedConfiguration n ≃
      CelestialOrderedConfiguration n where
  toFun := normalizedParavectorToCelestialOrdered n
  invFun := celestialToNormalizedParavectorOrdered n
  left_inv := by
    intro p
    apply Subtype.ext
    funext i
    exact normalizedNullParavectorEquivCelestial.symm_apply_apply (p.1 i)
  right_inv := by
    intro p
    apply Subtype.ext
    funext i
    exact normalizedNullParavectorEquivCelestial.apply_symm_apply (p.1 i)

/-- Pointwise lift of normalized null paravectors into the already established
ordered projective `Q55` null-boundary configurations. -/
def normalizedParavectorToQ55Configuration (n : ℕ) :
    NormalizedParavectorOrderedConfiguration n →
      NullOrderedConfiguration Q55 n :=
  celestialOrderedConfigurationMap n ∘
    normalizedParavectorToCelestialOrdered n

@[simp] theorem normalizedParavectorToQ55Configuration_apply
    (n : ℕ) (p : NormalizedParavectorOrderedConfiguration n) (i : Fin n) :
    (normalizedParavectorToQ55Configuration n p).1 i =
      celestialNullPoint
        (normalizedNullParavectorEquivCelestial (p.1 i)) :=
  rfl

/-- The pointwise boundary lift is injective on ordered configurations. -/
theorem normalizedParavectorToQ55Configuration_injective (n : ℕ) :
    Function.Injective (normalizedParavectorToQ55Configuration n) := by
  intro p q hpq
  apply (normalizedParavectorOrderedEquivCelestial n).injective
  apply celestialOrderedConfigurationMap_injective n
  exact hpq

/-- Reindex a normalized-paravector configuration by a finite permutation. -/
def normalizedParavectorPermute (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : NormalizedParavectorOrderedConfiguration n) :
    NormalizedParavectorOrderedConfiguration n := by
  refine ⟨fun i => p.1 (σ i), ?_⟩
  intro i j hij heq
  exact p.2 (σ i) (σ j) (fun h => hij (σ.injective h)) heq

/-- Normalization/celestial transport commutes exactly with particle
reindexing. -/
theorem normalizedParavectorToCelestialOrdered_respects_permute
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : NormalizedParavectorOrderedConfiguration n) :
    normalizedParavectorToCelestialOrdered n
        (normalizedParavectorPermute n σ p) =
      celestialPermute n σ (normalizedParavectorToCelestialOrdered n p) := by
  apply Subtype.ext
  funext i
  rfl

/-- The full projective-null configuration lift is permutation equivariant. -/
theorem normalizedParavectorToQ55Configuration_respects_permute
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (p : NormalizedParavectorOrderedConfiguration n) :
    normalizedParavectorToQ55Configuration n
        (normalizedParavectorPermute n σ p) =
      permute Q55 n σ (normalizedParavectorToQ55Configuration n p) := by
  change celestialOrderedConfigurationMap n
      (normalizedParavectorToCelestialOrdered n
        (normalizedParavectorPermute n σ p)) = _
  rw [normalizedParavectorToCelestialOrdered_respects_permute]
  exact celestialOrderedConfigurationMap_respects_permute n σ
    (normalizedParavectorToCelestialOrdered n p)

end InfoGeometry.Twistor.TwistorAnyonBoundaryConfiguration

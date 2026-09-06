import InfoGeometry.Topology.AmplituhedronSymbolicLatentBridge

/-!
# TopCat realization of the bounded amplituhedron latent readout

The quotient/readout triangle is made explicit as morphisms of `TopCat`.
This is a categorical presentation only; it adds no quotient identification
with a Grassmannian or with scattering data.
-/

namespace InfoGeometry.Topology

open CategoryTheory

variable {k n m : ℕ}

abbrev boundedAmplituhedronTopCatCarrier
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) : TopCat :=
  TopCat.of (BoundedAmplituhedronCarrier (k := k) Z B)

abbrev boundedAmplituhedronTopCatQuotient
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) : TopCat :=
  TopCat.of (ObservationalQuotient
    (boundedAmplituhedronLatentSystem (k := k) Z B))

abbrev boundedAmplituhedronTopCatReadout
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) : TopCat :=
  TopCat.of (Fin k × Fin m → ℝ)

noncomputable def boundedAmplituhedronTopCatProjection
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    boundedAmplituhedronTopCatCarrier (k := k) Z B ⟶
      boundedAmplituhedronTopCatQuotient (k := k) Z B :=
  TopCat.ofHom (ContinuousMap.mk
    (observationalQuotientMap
      (boundedAmplituhedronLatentSystem (k := k) Z B))
    (continuous_observationalQuotientMap
      (boundedAmplituhedronLatentSystem (k := k) Z B)))

noncomputable def boundedAmplituhedronTopCatReadoutHom
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    boundedAmplituhedronTopCatQuotient (k := k) Z B ⟶
      boundedAmplituhedronTopCatReadout (k := k) Z B :=
  TopCat.ofHom (ContinuousMap.mk
    (observationalQuotientReadout
      (boundedAmplituhedronLatentSystem (k := k) Z B))
    (continuous_observationalQuotientReadout
      (boundedAmplituhedronLatentSystem (k := k) Z B)))

noncomputable def boundedAmplituhedronTopCatObservationHom
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    boundedAmplituhedronTopCatCarrier (k := k) Z B ⟶
      boundedAmplituhedronTopCatReadout (k := k) Z B :=
  TopCat.ofHom (ContinuousMap.mk
    (boundedAmplituhedronObservationMap (k := k) Z B)
    (continuous_boundedAmplituhedronObservationMap Z B))

theorem boundedAmplituhedronTopCat_readout_triangle
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    boundedAmplituhedronTopCatProjection (k := k) Z B ≫
        boundedAmplituhedronTopCatReadoutHom (k := k) Z B =
      boundedAmplituhedronTopCatObservationHom (k := k) Z B := by
  ext x
  rfl

theorem boundedAmplituhedronTopCat_projection_isQuotientMap
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    Topology.IsQuotientMap
      (boundedAmplituhedronTopCatProjection (k := k) Z B) := by
  exact isQuotientMap_observationalQuotientMap
    (boundedAmplituhedronLatentSystem (k := k) Z B)

end InfoGeometry.Topology

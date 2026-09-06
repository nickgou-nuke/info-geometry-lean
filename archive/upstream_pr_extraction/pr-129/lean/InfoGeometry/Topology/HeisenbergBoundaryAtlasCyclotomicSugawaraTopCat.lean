import InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological

/-!
# TopCat packaging for the Heisenberg boundary / sixth-root / Sugawara packet

This file packages the already verified combined packet as a `TopCat`
object. It does not add any new algebraic identification; it only records
the projection to the input parameter and the canonical section given by the
combined readout.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopCat

open CategoryTheory
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological
open InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The combined packet as a `TopCat` object. -/
abbrev topCat : TopCat :=
  TopCat.of (BoundaryAtlasCyclotomicSugawaraPacket (𝕜 := 𝕜))

/-- The parameter space as a `TopCat` object. -/
abbrev parameterTopCat : TopCat :=
  TopCat.of (𝕜 × SixthRootParameter)

/-- Projection from the combined packet back to its input parameter. -/
noncomputable def projection :
    topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) :=
  TopCat.ofHom ⟨fun p => (p.1, p.2.1), continuous_of_discreteTopology⟩

/-- Canonical section from parameters into the combined packet. -/
noncomputable def atlasSection :
    parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) :=
  TopCat.ofHom ⟨boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜),
    continuous_boundaryAtlasCyclotomicSugawaraReadout (𝕜 := 𝕜)⟩

theorem atlasSection_projection :
    atlasSection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext p <;>
    simp [projection, atlasSection, boundaryAtlasCyclotomicSugawaraReadout,
      TopCat.comp_app, TopCat.ofHom]

end InfoGeometry.Topology.HeisenbergBoundaryAtlasCyclotomicSugawaraTopCat

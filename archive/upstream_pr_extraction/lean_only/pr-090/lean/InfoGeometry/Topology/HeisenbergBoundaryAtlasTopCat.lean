import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological

/-!
# TopCat packaging for the Heisenberg boundary atlas

This file packages the already-verified Heisenberg boundary atlas packet as a
`TopCat` object and records the canonical section/projection pair. The
topologies are discrete, so the categorical maps are bookkeeping consequences
of the existing algebraic atlas data.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergBoundaryAtlasTopCat

open CategoryTheory
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The Heisenberg boundary atlas packet as a `TopCat` object. -/
abbrev topCat : TopCat :=
  TopCat.of (HeisenbergBoundaryAtlasPacket (𝕜 := 𝕜))

/-- The parameter space of the Heisenberg boundary atlas as a `TopCat`
object. -/
abbrev parameterTopCat : TopCat :=
  TopCat.of 𝕜

/-- The canonical projection from the atlas packet to its parameter. -/
noncomputable def projection : topCat (𝕜 := 𝕜) ⟶ parameterTopCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun p => p.1, ?_⟩
  exact continuous_of_discreteTopology

/-- The canonical section of the atlas projection, built from the verified
atlas packet. -/
noncomputable def atlasSection : parameterTopCat (𝕜 := 𝕜) ⟶ topCat (𝕜 := 𝕜) := by
  refine TopCat.ofHom ?_
  refine ⟨fun α => topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜) α, ?_⟩
  simpa using continuous_topologicalHeisenbergBoundaryAtlas (𝕜 := 𝕜)

@[simp] theorem atlasSection_projection :
    atlasSection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext α
  rfl

@[simp] theorem atlasSection_projection_apply (α : 𝕜) :
    (atlasSection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)) α = α := by
  rfl

end InfoGeometry.Topology.HeisenbergBoundaryAtlasTopCat

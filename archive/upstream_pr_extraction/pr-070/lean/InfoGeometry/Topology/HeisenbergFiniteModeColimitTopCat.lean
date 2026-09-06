import Mathlib
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological

/-!
# TopCat packaging for the finite-mode Heisenberg colimit

This file packages the already-proved finite-mode Heisenberg exhaustion as a
discrete topological packet. The source is the finite-mode colimit carrier,
the target is the full Heisenberg algebra, and the section is obtained from the
existing surjective topological readout.

No new algebraic statement is introduced.
-/

noncomputable section

namespace InfoGeometry.Topology.HeisenbergFiniteModeColimitTopCat

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical
open VirasoroProject
open InfoGeometry.Topology.HeisenbergFiniteModeColimitTopological

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

instance heisenbergFiniteModeColimitTopologicalSpace :
    TopologicalSpace (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := ⊥

instance heisenbergFiniteModeColimitDiscreteTopology :
    DiscreteTopology (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := ⟨rfl⟩

instance heisenbergAlgebraTopologicalSpace :
    TopologicalSpace (HeisenbergAlgebra 𝕜) := ⊥

instance heisenbergAlgebraDiscreteTopology :
    DiscreteTopology (HeisenbergAlgebra 𝕜) := ⟨rfl⟩

/-- The canonical projection from the finite-mode colimit to the full Heisenberg carrier. -/
noncomputable def projection :
    TopCat.of (heisenbergFiniteModeColimit (𝕜 := 𝕜)) ⟶
      TopCat.of (HeisenbergAlgebra 𝕜) :=
  TopCat.ofHom
    { toFun := heisenbergFiniteModeColimitMap (𝕜 := 𝕜)
      continuous_toFun := continuous_of_discreteTopology }

/-- A canonical section chosen from the surjective finite-mode topological readout. -/
noncomputable def boundarySection :
    TopCat.of (HeisenbergAlgebra 𝕜) ⟶
      TopCat.of (heisenbergFiniteModeColimit (𝕜 := 𝕜)) := by
  refine TopCat.ofHom ?_
  refine ⟨(fun X : HeisenbergAlgebra 𝕜 => ?_), ?_⟩
  · have hsurj :
        ∃ y : ↑(heisenbergFiniteModeColimit (𝕜 := 𝕜)),
          (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom y = X := by
      simpa using
        (surjective_topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜) X)
    exact Classical.choose hsurj
  · exact continuous_of_discreteTopology

@[simp] theorem projection_boundarySection :
    boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜) = 𝟙 _ := by
  apply TopCat.hom_ext
  ext X
  change (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      (boundarySection (𝕜 := 𝕜) X) = X
  have hsurj :
      ∃ y : ↑(heisenbergFiniteModeColimit (𝕜 := 𝕜)),
        (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom y = X := by
    simpa using
      (surjective_topologicalHeisenbergFiniteModeColimitMap (𝕜 := 𝕜) X)
  simpa [boundarySection, projection] using
    (Classical.choose_spec hsurj)

@[simp] theorem projection_boundarySection_apply (X : HeisenbergAlgebra 𝕜) :
    (boundarySection (𝕜 := 𝕜) ≫ projection (𝕜 := 𝕜)).hom X = X := by
  simpa using (projection_boundarySection (𝕜 := 𝕜))

end InfoGeometry.Topology.HeisenbergFiniteModeColimitTopCat

import InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Heisenberg finite-mode filtered direct limit bridge

This owner exposes the finite-mode Heisenberg exhaustion through the generic
filtered-direct-limit API already present in the repository.

It does not add a completion, a topology, or a new algebraic structure.  It
simply identifies the existing finite-mode colimit map with the descended map
from the categorical direct-limit owner and records the stage law in that
language.
-/

noncomputable section

namespace InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge

open CategoryTheory CategoryTheory.Limits
open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-!
The compatibility name below is a transparent alias for the native
`ModuleCat` colimit.  No second direct-limit carrier or universal-property
wrapper is introduced here.
-/
abbrev heisenbergFiniteModeDirectLimit : ModuleCat 𝕜 :=
  heisenbergFiniteModeColimit (𝕜 := 𝕜)

/-- The generic filtered-direct-limit descent for the Heisenberg cocone. -/
noncomputable abbrev heisenbergFiniteModeDirectLimitMap :
    heisenbergFiniteModeDirectLimit (𝕜 := 𝕜) ⟶
      ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜) :=
  heisenbergFiniteModeColimitMap (𝕜 := 𝕜)

/-- The generic filtered-direct-limit map is the same map as the colimit readout. -/
@[simp] theorem heisenbergFiniteModeDirectLimitMap_eq :
    heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜) =
      heisenbergFiniteModeColimitMap (𝕜 := 𝕜) := by
  rfl

/-- The filtered-direct-limit stage law for the Heisenberg exhaustion. -/
theorem heisenbergFiniteModeDirectLimitMap_stage (s : Finset (Option ℤ)) :
    colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s ≫
      heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app s := by
  exact heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s

/-- The filtered-direct-limit map is surjective because it is the finite-mode colimit map. -/
theorem heisenbergFiniteModeDirectLimitMap_surjective :
    Function.Surjective
      (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom := by
  simpa using heisenbergFiniteModeColimitMap_surjective (𝕜 := 𝕜)

/-- A finite Heisenberg element is always represented by a direct-limit stage. -/
theorem heisenbergFiniteModeDirectLimit_boundaryReadout
    (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (heisenbergFiniteModeDirectLimitMap (𝕜 := 𝕜)).hom
            ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
  simpa [heisenbergFiniteModeDirectLimitMap_eq] using
    HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout
      (𝕜 := 𝕜) X

end InfoGeometry.Canonical.HeisenbergFiniteModeDirectLimitBridge

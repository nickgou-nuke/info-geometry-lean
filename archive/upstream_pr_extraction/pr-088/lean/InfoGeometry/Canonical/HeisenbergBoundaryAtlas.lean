import InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge
import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Heisenberg boundary atlas

This file does not claim a new algebraic morphism.  It packages the two
already-owned boundary surfaces for the Heisenberg corridor:

* the finite-mode colimit readout of the Heisenberg algebra;
* the current/Sugawara boundary representation on the charged Fock space.

The point is topological atlas-style bookkeeping, not new mathematics.
-/

namespace InfoGeometry.Canonical.HeisenbergBoundaryAtlas

open CategoryTheory
open CategoryTheory.Limits
open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraBridge

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Canonical atlas packet for the Heisenberg boundary corridor. -/
structure Atlas (α : 𝕜) where
  /-- The finite-mode colimit map from the Heisenberg exhaustion. -/
  finiteModeMap :
    heisenbergFiniteModeColimit (𝕜 := 𝕜) ⟶
      ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜)
  /-- The current Heisenberg representation on the charged Fock space. -/
  currentRep :
    CurrentHeisenbergRep 𝕜 (VirasoroProject.ChargedFockSpace 𝕜 α)

/-- The canonical atlas packet used by the repository. -/
noncomputable def canonicalAtlas (α : 𝕜) : Atlas (𝕜 := 𝕜) α where
  finiteModeMap := heisenbergFiniteModeColimitMap (𝕜 := 𝕜)
  currentRep := chargedFockSpaceCurrentHeisenbergRep 𝕜 α

@[simp] theorem canonicalAtlas_finiteModeMap (α : 𝕜) :
    (canonicalAtlas (𝕜 := 𝕜) α).finiteModeMap =
      heisenbergFiniteModeColimitMap (𝕜 := 𝕜) :=
  rfl

@[simp] theorem canonicalAtlas_currentRep (α : 𝕜) :
    (canonicalAtlas (𝕜 := 𝕜) α).currentRep =
      chargedFockSpaceCurrentHeisenbergRep 𝕜 α :=
  rfl

/-- The finite-mode boundary readout is available from the canonical atlas. -/
theorem canonicalAtlas_finiteMode_boundaryReadout
    (α : 𝕜) (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (canonicalAtlas (𝕜 := 𝕜) α).finiteModeMap.hom
            ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
  simpa [canonicalAtlas] using
    HeisenbergFiniteModeBoundaryBridge.heisenbergFiniteMode_boundaryReadout
      (𝕜 := 𝕜) X

/-- The Sugawara central boundary readout is available from the canonical atlas. -/
theorem canonicalAtlas_currentSugawara_central
    (α : 𝕜) :
    (canonicalAtlas (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.cgen 𝕜) =
      (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) :=
  CurrentHeisenbergRep.currentSugawaraRepresentation_central
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α)

/-- The atlas still exposes the `lgen` readout of the current boundary. -/
theorem canonicalAtlas_currentSugawara_lgen_apply
    (α : 𝕜) (n : Int) :
    (canonicalAtlas (𝕜 := 𝕜) α).currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 n) =
      (canonicalAtlas (𝕜 := 𝕜) α).currentRep.sugawaraStressMode n :=
  CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α) n

end InfoGeometry.Canonical.HeisenbergBoundaryAtlas

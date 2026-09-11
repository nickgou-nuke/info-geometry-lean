import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Boundary readout for the finite-mode Heisenberg colimit

This owner packages the already-proved finite-support exhaustion of the
Heisenberg algebra into a boundary-facing statement:

* every Heisenberg element lies in some finite stage;
* the filtered colimit map agrees with the stage inclusion;
* therefore every Heisenberg element is recovered from a finite-stage colimit
  representative.

It does not add a new current algebra or a topological completion.
-/

namespace InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge

open CategoryTheory CategoryTheory.Limits
open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Every Heisenberg element is represented by a finite-mode colimit stage. -/
theorem heisenbergFiniteMode_boundaryReadout
    (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
            ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
  rcases heisenberg_mem_finiteModeStage (𝕜 := 𝕜) X with ⟨s, hX⟩
  refine ⟨s, ⟨X, hX⟩, ?_⟩
  have hstage := congrArg (fun f => f.hom) (heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s)
  exact congrArg (fun g => g (⟨X, hX⟩ : heisenbergFiniteModeStage (𝕜 := 𝕜) s)) hstage

/-- The canonical colimit map is stage-wise exhaustive on the Heisenberg basis. -/
theorem heisenbergFiniteMode_boundaryReadout_basis
    (k : Option ℤ) :
    ∃ s : Finset (Option ℤ),
      HeisenbergAlgebra.basisJK 𝕜 k ∈ heisenbergFiniteModeStage (𝕜 := 𝕜) s := by
  exact ⟨{k}, basisJK_mem_heisenbergFiniteModeStage (𝕜 := 𝕜) {k} k (by simp)⟩

end InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge

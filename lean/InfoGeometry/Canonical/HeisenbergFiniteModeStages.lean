import InfoGeometry.External.Virasoro.HeisenbergAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.ToMathlib.LinearAlgebra.Basis.FinsumRepr

/-!
# Finite-support stages for the Heisenberg algebra

The Heisenberg owner is a central extension of the finitely-supported mode
space.  This file records the algebraic exhaustion by finite subsets of its
standard `Jₖ,K` basis.  It is deliberately prior to a categorical colimit:
the stage inclusions and their cocone still have to be packaged separately.
-/

namespace InfoGeometry.Canonical

open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

noncomputable def heisenbergFiniteModeStage
    (s : Finset (Option ℤ)) :
    Submodule 𝕜 (HeisenbergAlgebra 𝕜) :=
  Submodule.span 𝕜 ((HeisenbergAlgebra.basisJK 𝕜) '' (s : Set (Option ℤ)))

theorem basisJK_mem_heisenbergFiniteModeStage
    (s : Finset (Option ℤ)) (i : Option ℤ) (hi : i ∈ s) :
    HeisenbergAlgebra.basisJK 𝕜 i ∈ heisenbergFiniteModeStage (𝕜 := 𝕜) s := by
  apply Submodule.subset_span
  exact Set.mem_image_of_mem _ hi

theorem heisenberg_mem_finiteModeStage
    (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      X ∈ heisenbergFiniteModeStage (𝕜 := 𝕜) s := by
  let cf := (HeisenbergAlgebra.basisJK 𝕜).repr X
  refine ⟨cf.support, ?_⟩
  change X ∈ Submodule.span 𝕜
    ((HeisenbergAlgebra.basisJK 𝕜) '' (cf.support : Set (Option ℤ)))
  rw [Module.Basis.mem_span_image]

theorem heisenberg_mode_stage_contains_jgen
    (k : ℤ) :
    HeisenbergAlgebra.jgen 𝕜 k ∈
      heisenbergFiniteModeStage (𝕜 := 𝕜) {some k} := by
  simpa using
    (basisJK_mem_heisenbergFiniteModeStage (𝕜 := 𝕜)
      ({some k} : Finset (Option ℤ)) (some k) (by simp))

theorem heisenberg_mode_stage_contains_kgen :
    HeisenbergAlgebra.kgen 𝕜 ∈
      heisenbergFiniteModeStage (𝕜 := 𝕜) {none} := by
  simpa using
    (basisJK_mem_heisenbergFiniteModeStage (𝕜 := 𝕜)
      ({none} : Finset (Option ℤ)) none (by simp))

end InfoGeometry.Canonical

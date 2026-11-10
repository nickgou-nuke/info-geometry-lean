/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Virasoro.HeisenbergAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.ToMathlib.LinearAlgebra.Basis.FinsumRepr

/-!
# Finite-support stages for the Heisenberg algebra

The Heisenberg owner is a central extension of the finitely-supported mode
space.  This file records the algebraic exhaustion by finite subsets of its
standard `Jₖ,K` basis.

- BUCKET 1 (Real Math in This File):
  - `heisenbergFiniteModeStage`, `basisJK_mem_heisenbergFiniteModeStage`
  - `heisenberg_mem_finiteModeStage`, `heisenberg_mode_stage_contains_jgen`,
    `heisenberg_mode_stage_contains_kgen`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.External.Virasoro.HeisenbergAlgebra`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Canonical

open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Linear submodule of `HeisenbergAlgebra 𝕜` spanned by the basis vectors
`HeisenbergAlgebra.basisJK 𝕜 i` for `i ∈ s`. -/
noncomputable def heisenbergFiniteModeStage
    (s : Finset (Option ℤ)) :
    Submodule 𝕜 (HeisenbergAlgebra 𝕜) :=
  Submodule.span 𝕜 ((HeisenbergAlgebra.basisJK 𝕜) '' (s : Set (Option ℤ)))

/-- Every basis vector `basisJK 𝕜 i` with `i ∈ s` belongs to `heisenbergFiniteModeStage s`. -/
theorem basisJK_mem_heisenbergFiniteModeStage
    (s : Finset (Option ℤ)) (i : Option ℤ) (hi : i ∈ s) :
    HeisenbergAlgebra.basisJK 𝕜 i ∈ heisenbergFiniteModeStage (𝕜 := 𝕜) s := by
  apply Submodule.subset_span
  exact Set.mem_image_of_mem _ hi

/-- Every element of `HeisenbergAlgebra 𝕜` belongs to `heisenbergFiniteModeStage s`
for some finite index set `s : Finset (Option ℤ)`. -/
theorem heisenberg_mem_finiteModeStage
    (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      X ∈ heisenbergFiniteModeStage (𝕜 := 𝕜) s := by
  let cf := (HeisenbergAlgebra.basisJK 𝕜).repr X
  refine ⟨cf.support, ?_⟩
  change X ∈ Submodule.span 𝕜
    ((HeisenbergAlgebra.basisJK 𝕜) '' (cf.support : Set (Option ℤ)))
  rw [Module.Basis.mem_span_image]

/-- The mode generator `jgen 𝕜 k` belongs to the singleton stage `heisenbergFiniteModeStage {some k}`. -/
theorem heisenberg_mode_stage_contains_jgen
    (k : ℤ) :
    HeisenbergAlgebra.jgen 𝕜 k ∈
      heisenbergFiniteModeStage (𝕜 := 𝕜) {some k} := by
  simpa using
    (basisJK_mem_heisenbergFiniteModeStage (𝕜 := 𝕜)
      ({some k} : Finset (Option ℤ)) (some k) (Finset.mem_singleton_self _))

/-- The central generator `kgen 𝕜` belongs to the singleton stage `heisenbergFiniteModeStage {none}`. -/
theorem heisenberg_mode_stage_contains_kgen :
    HeisenbergAlgebra.kgen 𝕜 ∈
      heisenbergFiniteModeStage (𝕜 := 𝕜) {none} := by
  simpa using
    (basisJK_mem_heisenbergFiniteModeStage (𝕜 := 𝕜)
      ({none} : Finset (Option ℤ)) none (Finset.mem_singleton_self _))

end InfoGeometry.Canonical

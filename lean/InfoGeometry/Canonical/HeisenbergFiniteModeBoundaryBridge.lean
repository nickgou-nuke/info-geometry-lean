/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Boundary Readout for the Finite-Mode Heisenberg Colimit

This module establishes the boundary stage-exhaustion theorems for the filtered
`ModuleCat 𝕜` colimit of the Heisenberg algebra:

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeStages`: `heisenbergFiniteModeStage`,
    `basisJK_mem_heisenbergFiniteModeStage`, `heisenberg_mem_finiteModeStage`.
  * `InfoGeometry.Canonical.HeisenbergFiniteModeColimit`: `heisenbergFiniteModeDiagram`,
    `heisenbergFiniteModeColimitMap`, `heisenbergFiniteModeColimitMap_stage`.
- BUCKET 2 (Deconfabulation):
  * Replaced implicit `simp` closure in `heisenbergFiniteMode_boundaryReadout_basis`
    with an explicit singleton membership witness `Finset.mem_singleton_self`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergFiniteMode_boundaryReadout`: every $X \in \mathrm{HeisenbergAlgebra}(\mathbb{k})$
    is recovered via `heisenbergFiniteModeColimitMap` from a finite-support stage
    $s \subset \mathrm{Option}\,\mathbb{Z}$.
  * `heisenbergFiniteMode_boundaryReadout_basis`: every standard basis vector
    `HeisenbergAlgebra.basisJK 𝕜 k` lies in its singleton stage `{k}`.
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

/-- The canonical colimit exhaustion is stage-wise exhaustive on the Heisenberg basis. -/
theorem heisenbergFiniteMode_boundaryReadout_basis
    (k : Option ℤ) :
    ∃ s : Finset (Option ℤ),
      HeisenbergAlgebra.basisJK 𝕜 k ∈ heisenbergFiniteModeStage (𝕜 := 𝕜) s := by
  have hk : k ∈ ({k} : Finset (Option ℤ)) := Finset.mem_singleton_self k
  exact ⟨{k}, basisJK_mem_heisenbergFiniteModeStage (𝕜 := 𝕜) {k} k hk⟩

end InfoGeometry.Canonical.HeisenbergFiniteModeBoundaryBridge

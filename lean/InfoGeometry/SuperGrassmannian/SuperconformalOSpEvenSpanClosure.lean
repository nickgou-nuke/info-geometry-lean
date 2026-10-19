/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

namespace InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.MatrixSpans

open InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair

variable {R : Type*} [CommRing R]

/-- The concrete graded even span lies in the kernel of the OSp supertrace.
This packages the vanishing on the three structure generators as a closure
statement for arbitrary finite linear combinations. -/
theorem evenSpan_supertrace_zero {x : M R} (hx : x ∈ evenSpan) :
    supertrace x = 0 := by
  have h_add (a b : M R) : supertrace (a + b) = supertrace a + supertrace b := by
    dsimp [supertrace]
    ring
  have h_smul (r : R) (a : M R) : supertrace (r • a) = r * supertrace a := by
    dsimp [supertrace]
    ring
  refine Submodule.span_induction
    (p := fun a _ => supertrace a = 0)
    ?_ ?_ ?_ ?_ hx
  · intro a ha
    rcases ha with ⟨i, rfl⟩
    cases i <;>
      simp [evenBasis, supertrace, H_gen, E_gen, F_gen, E]
  · simp [supertrace]
  · intro a b _ _ ha hb
    rw [h_add, ha, hb]
    simp
  · intro r a _ ha
    rw [h_smul, ha]
    simp

end InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.MatrixSpans

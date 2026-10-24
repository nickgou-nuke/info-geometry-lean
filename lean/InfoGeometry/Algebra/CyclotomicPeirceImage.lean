/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CyclotomicPeirceMatrix
import InfoGeometry.Core.FinitePeirceMatrix

/-! # Exact image of the cyclotomic Peirce representation

The image unit is `Matrix.diagonal F.projector`; it need not equal the ambient
matrix unit. Each supported corner array reconstructs a unique operator.
-/
namespace InfoGeometry.Algebra.CyclotomicPeirceMatrix
open InfoGeometry.Canonical.CyclotomicProjector
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {U : A} {n : ℕ} (F : FourierCyclotomicReadout (K := K) U n)

/-- Entrywise corner support characterizes the image, including uniqueness. -/
theorem existsUnique_blocks_iff_supported (B : Matrix (Fin n) (Fin n) A) :
    (∃! X : A, blocks F X = B) ↔
      ∀ i j, F.projector i * B i j * F.projector j = B i j := by
  constructor
  · rintro ⟨X, rfl, _⟩
    exact blocks_supported F X
  · intro hB
    have he : CompleteOrthogonalIdempotents F.projector :=
      { idem := F.idempotent
        ortho := F.orthogonal
        complete := F.complete }
    let C : InfoGeometry.Core.FinitePeirceMatrix.cornerSpace (K := K) F.projector :=
      ⟨B, hB⟩
    have hcut : blocks F (∑ i, ∑ j, B i j) = B :=
      InfoGeometry.Core.FinitePeirceMatrix.blocks_assemble
        F.projector he.toOrthogonalIdempotents C
    refine ⟨∑ i, ∑ j, B i j, hcut, ?_⟩
    intro X hX
    exact blocks_injective F (hX.trans hcut.symm)

end InfoGeometry.Algebra.CyclotomicPeirceMatrix

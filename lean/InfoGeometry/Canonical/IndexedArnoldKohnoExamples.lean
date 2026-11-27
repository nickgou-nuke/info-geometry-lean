/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.IndexedArnoldKohnoExterior
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Noncommuting real residue examples

The explicit residue pair has nonzero commutator. It nevertheless satisfies
the three-channel cancellation when the third residue is the negative sum.
This checks that the operator-valued result is not restricted to scalar or
pairwise commuting residue data.
-/

noncomputable section

namespace InfoGeometry.Canonical.IndexedArnoldKohnoExterior.Examples

open InfoGeometry.Canonical.IndexedArnoldKZComplex
open InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection

attribute [local instance] LieRing.ofAssociativeRing

private def upper : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
private def lower : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The real matrix residue carrier has a closed noncommutativity witness. -/
theorem real_matrix_noncommutative :
    ∃ x y : Matrix (Fin 2) (Fin 2) ℝ, x * y ≠ y * x := by
  refine ⟨upper, lower, ?_⟩
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  norm_num [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Concrete real matrices with a nonzero residue commutator satisfy the
native tensor-valued Arnold--Kohno cancellation. -/
theorem real_noncommuting_triangle (z : Conf 3 ℝ) (dz : Fin 3 → (Fin 3 → ℝ)) :
    ∃ x y : Matrix (Fin 2) (Fin 2) ℝ,
      ⁅x, y⁆ ≠ 0 ∧
        triangleCurvature x y (-(x + y))
          (dlogExterior z dz 0 1) (dlogExterior z dz 1 2)
          (dlogExterior z dz 2 0) = 0 := by
  obtain ⟨x, y, hxy⟩ := real_matrix_noncommutative
  refine ⟨x, y, ?_, triangle_negative_sum_eq_zero z dz x y⟩
  change x * y - y * x ≠ 0
  intro h
  exact hxy (sub_eq_zero.mp h)

end InfoGeometry.Canonical.IndexedArnoldKohnoExterior.Examples

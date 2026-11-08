/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectLevelSet
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import Mathlib.Algebra.Group.Torsion

/-!
# Incompatible identities on the unit defect level set

The submitted A₃₈ cubic and A₄₃ geometric truncation each force V = 0,
whereas δ(V) = 1 excludes V = 0 in a nontrivial ring. The submitted
left-only A₃₀ Laplacian also fails at the identity when doubling is injective.
All operators are the existing Peirce operators in the ambient ring.

Dependencies: exact defect remainder criteria → nonzero unit level → exclusions.
These are conditional exclusions on the level set, not an existence theorem
for that level set in every ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B] [Nontrivial B] {P A C : B}

theorem genV_ne_zero_of_unit_defect
    (hV : idempotencyDefect (genV P A C) = 1) : genV P A C ≠ 0 := by
  intro hzero
  rw [hzero] at hV
  simp [idempotencyDefect] at hV

theorem unit_defect_excludes_submitted_cubic
    (hV : idempotencyDefect (genV P A C) = 1) :
    genV P A C * genV P A C * genV P A C - genV P A C * genV P A C -
      genV P A C ≠ genV P A C * idempotencyDefect (genV P A C) := by
  intro h
  exact genV_ne_zero_of_unit_defect hV
    ((incorrect_cube_recurrence_iff_zero _).mp h)

theorem unit_defect_excludes_submitted_geometric_remainder
    (hV : idempotencyDefect (genV P A C) = 1) :
    (1 - genV P A C) * (1 + genV P A C + genV P A C * genV P A C) - 1 ≠
      -((1 + genV P A C) * idempotencyDefect (genV P A C)) := by
  intro h
  exact genV_ne_zero_of_unit_defect hV
    ((geometricSum_three_omitted_term_iff_zero _).mp h)

theorem unit_defect_excludes_left_only_laplacian [IsAddTorsionFree B]
    (hP : P * P = P) (hV : idempotencyDefect (genV P A C) = 1) :
    hodgeLaplacianPhi P A C 1 ≠ (2 : ℤ) • (genV P A C * 1) := by
  intro h
  have htwo := (hodgeLaplacianPhi_left_only_iff hP A C 1).mp h
  apply genV_ne_zero_of_unit_defect hV
  apply IsAddTorsionFree.nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  simpa only [one_mul, two_zsmul, two_nsmul, smul_zero] using htwo

end InfoGeometry.OperatorAlgebra.PeirceSpine

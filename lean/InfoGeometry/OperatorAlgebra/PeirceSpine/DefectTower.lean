/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentDefectIteration
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Defect iteration on orthogonal Peirce cycles

The generic defect polynomial and its dyadic identities live in
`Core.IdempotentGraphGrassmannian`. This file specializes its orthogonal
iteration theorem to the two operator cycles `Q₊ = N₊N₋` and `Q₋ = N₋N₊`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- The two Peirce cycles are orthogonal in both orders. -/
theorem qgt_cycles_orthogonal (A C : B) :
    qgtPlus P A C * qgtMinus P A C = 0 ∧
    qgtMinus P A C * qgtPlus P A C = 0 := by
  constructor <;> (simp only [qgtPlus, qgtMinus]; peirce_nf hP)

/-- The first idempotency defect splits additively over the two Peirce cycles. -/
theorem genV_defect_cycle_split (A C : B) :
    idempotencyDefect (genV P A C) =
      idempotencyDefect (qgtPlus P A C) + idempotencyDefect (qgtMinus P A C) := by
  change idempotencyDefect (qgtPlus P A C + qgtMinus P A C) = _
  exact idempotencyDefect_add_of_orthogonal
    (qgt_cycles_orthogonal hP A C).1 (qgt_cycles_orthogonal hP A C).2

/-- The second defect iterate also splits over the orthogonal Peirce cycles. -/
theorem genV_defect_iterate_cycle_split (A C : B) :
    idempotencyDefect (idempotencyDefect (genV P A C)) =
      idempotencyDefect (idempotencyDefect (qgtPlus P A C)) +
        idempotencyDefect (idempotencyDefect (qgtMinus P A C)) := by
  change idempotencyDefect (idempotencyDefect (qgtPlus P A C + qgtMinus P A C)) = _
  exact idempotencyDefect_iterate_add_of_orthogonal
    (qgt_cycles_orthogonal hP A C).1 (qgt_cycles_orthogonal hP A C).2

/-- Every finite defect iterate splits over the two Peirce cycles. -/
theorem genV_defect_iterates_cycle_split (A C : B) (n : ℕ) :
    idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) +
        idempotencyDefect^[n] (qgtMinus P A C) := by
  change idempotencyDefect^[n] (qgtPlus P A C + qgtMinus P A C) = _
  exact idempotencyDefect_iterates_add_of_orthogonal
    (qgt_cycles_orthogonal hP A C).1 (qgt_cycles_orthogonal hP A C).2 n

/-- The two iterated cycles still annihilate each other in both orders. -/
theorem qgt_defect_iterates_orthogonal (A C : B) (n : ℕ) :
    idempotencyDefect^[n] (qgtPlus P A C) *
        idempotencyDefect^[n] (qgtMinus P A C) = 0 ∧
    idempotencyDefect^[n] (qgtMinus P A C) *
        idempotencyDefect^[n] (qgtPlus P A C) = 0 := by
  exact ⟨idempotencyDefect_iterates_mul_eq_zero (qgt_cycles_orthogonal hP A C).1 n,
    idempotencyDefect_iterates_mul_eq_zero (qgt_cycles_orthogonal hP A C).2 n⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine

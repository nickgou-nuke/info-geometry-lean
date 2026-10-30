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

/-- Upper-cycle left support is preserved at every finite depth. -/
theorem qgtPlus_defect_iterates_left (A C : B) (n : ℕ) :
    P * idempotencyDefect^[n] (qgtPlus P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) := by
  apply idempotencyDefect_iterates_left_support
  simp only [qgtPlus]
  peirce_nf hP

theorem qgtPlus_defect_iterates_right (A C : B) (n : ℕ) :
    idempotencyDefect^[n] (qgtPlus P A C) * P =
      idempotencyDefect^[n] (qgtPlus P A C) := by
  apply idempotencyDefect_iterates_right_support
  simp only [qgtPlus]
  peirce_nf hP

/-- Lower-cycle left support remains in the complementary corner. -/
theorem qgtMinus_defect_iterates_left (A C : B) (n : ℕ) :
    (1 - P) * idempotencyDefect^[n] (qgtMinus P A C) =
      idempotencyDefect^[n] (qgtMinus P A C) := by
  apply idempotencyDefect_iterates_left_support
  simp only [qgtMinus]
  peirce_nf hP

theorem qgtMinus_defect_iterates_right (A C : B) (n : ℕ) :
    idempotencyDefect^[n] (qgtMinus P A C) * (1 - P) =
      idempotencyDefect^[n] (qgtMinus P A C) := by
  apply idempotencyDefect_iterates_right_support
  simp only [qgtMinus]
  peirce_nf hP

/-- Left projection extracts exactly the upper iterated cycle. -/
theorem genV_defect_iterates_left_projection (A C : B) (n : ℕ) :
    P * idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) := by
  have hz := qgtMinus_defect_iterates_left hP A C n
  simp only [sub_mul, one_mul, sub_eq_self] at hz
  rw [genV_defect_iterates_cycle_split hP, mul_add,
    qgtPlus_defect_iterates_left hP, hz, add_zero]

/-- Right projection extracts the same cycle without imposing ambient commutativity. -/
theorem genV_defect_iterates_right_projection (A C : B) (n : ℕ) :
    idempotencyDefect^[n] (genV P A C) * P =
      idempotencyDefect^[n] (qgtPlus P A C) := by
  have hz := qgtMinus_defect_iterates_right hP A C n
  simp only [mul_sub, mul_one, sub_eq_self] at hz
  rw [genV_defect_iterates_cycle_split hP, add_mul,
    qgtPlus_defect_iterates_right hP, hz, add_zero]

/-- Left ideal projection selects the upper off-diagonal component at every depth. -/
theorem genPhi_defect_iterates_left (A C : B) (n : ℕ) :
    P * (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
      conePlus P A * idempotencyDefect^[n] (genV P A C) := by
  simp only [genPhi, add_mul, mul_add, ← mul_assoc,
    P_mul_conePlus hP, P_mul_coneMinus hP, zero_mul, add_zero]

/-- Right ideal projection selects the opposite component, retaining operator order. -/
theorem genPhi_defect_iterates_right (A C : B) (n : ℕ) :
    (genPhi P A C * idempotencyDefect^[n] (genV P A C)) * P =
      coneMinus P C * idempotencyDefect^[n] (genV P A C) := by
  have hcomm : idempotencyDefect^[n] (genV P A C) * P =
      P * idempotencyDefect^[n] (genV P A C) := by
    rw [genV_defect_iterates_right_projection hP,
      genV_defect_iterates_left_projection hP]
  rw [mul_assoc, hcomm, ← mul_assoc]
  simp only [genPhi, add_mul, conePlus_mul_P hP, coneMinus_mul_P hP,
    zero_add]

/-- The complementary left projection extracts the lower cycle. -/
theorem genV_defect_iterates_complement_left (A C : B) (n : ℕ) :
    (1 - P) * idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (qgtMinus P A C) := by
  rw [sub_mul, one_mul, genV_defect_iterates_left_projection hP,
    genV_defect_iterates_cycle_split hP]
  abel

theorem genV_defect_iterates_complement_right (A C : B) (n : ℕ) :
    idempotencyDefect^[n] (genV P A C) * (1 - P) =
      idempotencyDefect^[n] (qgtMinus P A C) := by
  rw [mul_sub, mul_one, genV_defect_iterates_right_projection hP,
    genV_defect_iterates_cycle_split hP]
  abel

/-- The upper off-diagonal operator acts only on the lower input cycle. -/
theorem conePlus_defect_iterates_lower (A C : B) (n : ℕ) :
    conePlus P A * idempotencyDefect^[n] (genV P A C) =
      conePlus P A * idempotencyDefect^[n] (qgtMinus P A C) := by
  rw [← genV_defect_iterates_complement_left hP A C n, ← mul_assoc]
  simp only [mul_sub, mul_one, conePlus_mul_P hP, sub_zero]

/-- The lower off-diagonal operator acts only on the upper input cycle. -/
theorem coneMinus_defect_iterates_upper (A C : B) (n : ℕ) :
    coneMinus P C * idempotencyDefect^[n] (genV P A C) =
      coneMinus P C * idempotencyDefect^[n] (qgtPlus P A C) := by
  rw [← genV_defect_iterates_left_projection hP A C n, ← mul_assoc,
    coneMinus_mul_P hP]

end InfoGeometry.OperatorAlgebra.PeirceSpine

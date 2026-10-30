/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Block-triangular operators and idempotent compression

For an idempotent `P` in an arbitrary associative ring, define a lower
two-corner operator by its `11`, `01`, and `00` Peirce blocks. These blocks
are closed under multiplication. A second idempotent orthogonal to `P`
defines a bilateral compression whose square is itself and whose `11` block
is unchanged.

This is the algebraic content of the A85 intake. No attention, token, or
causal interpretation is part of these statements.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The sum of the `11`, `01`, and `00` blocks relative to `P`. -/
def blockLower (P F L D : B) : B :=
  peirce11 P F + coneMinus P L + peirce00 P D

/-- Bilateral compression by the complement of an idempotent. -/
def idempotentCompression (Q T : B) : B := (1 - Q) * T * (1 - Q)

/-- The part removed by bilateral compression, expanded without assuming that
the target commutes with the operator being compressed. -/
theorem idempotentCompression_removed_terms (Q T : B) :
    T - idempotentCompression Q T = Q * T + T * Q - Q * T * Q := by
  unfold idempotentCompression
  noncomm_ring

section BlockLower

variable {P Q : B} (hP : P * P = P)
include hP

/-- A lower block operator has zero upper-right corner. -/
theorem blockLower_upper_right (F L D : B) :
    P * blockLower P F L D * (1 - P) = 0 := by
  unfold blockLower peirce11 coneMinus peirce00
  peirce_nf hP

/-- The `11` block of a lower block operator is its factual `11` input. -/
theorem blockLower_peirce11 (F L D : B) :
    peirce11 P (blockLower P F L D) = peirce11 P F := by
  unfold blockLower peirce11 coneMinus peirce00
  peirce_nf hP

/-- The `01` block of a lower block operator is its cross-corner input. -/
theorem blockLower_coneMinus (F L D : B) :
    coneMinus P (blockLower P F L D) = coneMinus P L := by
  unfold blockLower coneMinus peirce11 peirce00
  peirce_nf hP

/-- The `00` block of a lower block operator is its event-corner input. -/
theorem blockLower_peirce00 (F L D : B) :
    peirce00 P (blockLower P F L D) = peirce00 P D := by
  unfold blockLower peirce00 coneMinus peirce11
  peirce_nf hP

/-- Product of lower block operators, expressed in its three Peirce blocks. -/
theorem blockLower_mul (F₁ L₁ D₁ F₂ L₂ D₂ : B) :
    blockLower P F₁ L₁ D₁ * blockLower P F₂ L₂ D₂ =
      blockLower P (F₁ * P * F₂)
        (L₁ * P * F₂ + D₁ * (1 - P) * L₂)
        (D₁ * (1 - P) * D₂) := by
  unfold blockLower coneMinus peirce11 peirce00
  peirce_nf hP

end BlockLower

section Compression

variable {Q : B} (hQ : Q * Q = Q)
include hQ

/-- Bilateral compression by an idempotent complement is idempotent as a map. -/
theorem idempotentCompression_idempotent (T : B) :
    idempotentCompression Q (idempotentCompression Q T) =
      idempotentCompression Q T := by
  have hcomp : (1 - Q) * (1 - Q) = 1 - Q := by
    noncomm_ring [hQ]
  unfold idempotentCompression
  calc
    (1 - Q) * ((1 - Q) * T * (1 - Q)) * (1 - Q) =
        ((1 - Q) * (1 - Q)) * T * ((1 - Q) * (1 - Q)) := by
          noncomm_ring
    _ = (1 - Q) * T * (1 - Q) := by rw [hcomp]

/-- The compressed operator is annihilated on the left by the target idempotent. -/
theorem idempotentCompression_left_zero (T : B) :
    Q * idempotentCompression Q T = 0 := by
  have hcomp : Q * (1 - Q) = 0 := by
    noncomm_ring [hQ]
  unfold idempotentCompression
  calc
    Q * ((1 - Q) * T * (1 - Q)) = (Q * (1 - Q)) * (T * (1 - Q)) := by
      simp only [mul_assoc]
    _ = 0 := by rw [hcomp, zero_mul]

/-- The compressed operator is annihilated on the right by the target idempotent. -/
theorem idempotentCompression_right_zero (T : B) :
    idempotentCompression Q T * Q = 0 := by
  have hcomp : (1 - Q) * Q = 0 := by
    noncomm_ring [hQ]
  unfold idempotentCompression
  calc
    ((1 - Q) * T * (1 - Q)) * Q = ((1 - Q) * T) * ((1 - Q) * Q) := by
      simp only [mul_assoc]
    _ = 0 := by rw [hcomp, mul_zero]

end Compression

section CornerPreservation

variable {P Q : B} (hPQ : P * Q = 0) (hQP : Q * P = 0)
include hPQ hQP

/-- Compression by an orthogonal idempotent preserves the `11` block. -/
theorem idempotentCompression_peirce11 (T : B) :
    peirce11 P (idempotentCompression Q T) = peirce11 P T := by
  unfold peirce11 idempotentCompression
  have hPQ_assoc : ∀ X : B, P * (Q * X) = 0 := by
    intro X
    rw [← mul_assoc, hPQ, zero_mul]
  have hQP_assoc : ∀ X : B, Q * (P * X) = 0 := by
    intro X
    rw [← mul_assoc, hQP, zero_mul]
  simp only [sub_mul, mul_sub, one_mul, mul_one,
    mul_assoc, hQP, hPQ_assoc,
    mul_zero, zero_mul]
  abel

/-- The intervention difference has zero `11` Peirce block when its target
idempotent is orthogonal to `P` on both sides. -/
theorem idempotentCompression_removed_peirce11 (T : B) :
    peirce11 P (T - idempotentCompression Q T) = 0 := by
  calc
    peirce11 P (T - idempotentCompression Q T) =
        peirce11 P T - peirce11 P (idempotentCompression Q T) := by
          unfold peirce11
          noncomm_ring
    _ = 0 := by
      rw [idempotentCompression_peirce11 hPQ hQP T]
      exact sub_self _

end CornerPreservation

end InfoGeometry.OperatorAlgebra.PeirceSpine

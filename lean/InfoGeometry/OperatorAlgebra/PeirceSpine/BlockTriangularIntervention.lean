/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower

/-!
# Block-triangular operators and idempotent compression

For an idempotent `P` in an arbitrary associative ring, define a lower
two-corner operator by its `11`, `01`, and `00` Peirce blocks. These blocks
are closed under multiplication. A second idempotent orthogonal to `P`
defines a bilateral compression whose square is itself and whose `11` block
is unchanged.

This is the algebraic content of the A85–A86 intake. No attention, token, or
causal interpretation is part of these statements.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

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

section RemovedCorner

variable {Q : B} (hQ : Q * Q = Q)
include hQ

/-- Left multiplication by the target idempotent recovers the entire left
incident part removed by complementary-corner compression. -/
theorem idempotentCompression_removed_left (T : B) :
    Q * (T - idempotentCompression Q T) = Q * T := by
  have hcomp : Q * (1 - Q) = 0 := by noncomm_ring [hQ]
  unfold idempotentCompression
  calc
    Q * (T - (1 - Q) * T * (1 - Q)) =
        Q * T - (Q * (1 - Q)) * T * (1 - Q) := by noncomm_ring
    _ = Q * T := by rw [hcomp]; simp

/-- Right multiplication by the target idempotent recovers the entire right
incident part removed by complementary-corner compression. -/
theorem idempotentCompression_removed_right (T : B) :
    (T - idempotentCompression Q T) * Q = T * Q := by
  have hcomp : (1 - Q) * Q = 0 := by noncomm_ring [hQ]
  unfold idempotentCompression
  calc
    (T - (1 - Q) * T * (1 - Q)) * Q =
        T * Q - (1 - Q) * T * ((1 - Q) * Q) := by noncomm_ring
    _ = T * Q := by rw [hcomp]; simp

/-- Compression to the complementary corner annihilates the removed part. -/
theorem idempotentCompression_removed_complementary_corner (T : B) :
    (1 - Q) * (T - idempotentCompression Q T) * (1 - Q) = 0 := by
  have hcomp : (1 - Q) * (1 - Q) = 1 - Q := by noncomm_ring [hQ]
  unfold idempotentCompression
  calc
    (1 - Q) * (T - (1 - Q) * T * (1 - Q)) * (1 - Q) =
        (1 - Q) * T * (1 - Q) - ((1 - Q) * (1 - Q)) * T *
          ((1 - Q) * (1 - Q)) := by noncomm_ring
    _ = 0 := by rw [hcomp]; simp

end RemovedCorner

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

/-- At every defect depth `n`, the lower-triangular Peirce assembly with
diagonal input `δ^[n](V)` and cross-corner input `Φ δ^[n](V)` equals
`(1 + N₋) δ^[n](V)` (`A86`). -/
theorem blockLower_genV_defect_iterate (A C : B) (n : ℕ) :
    blockLower P
      (idempotencyDefect^[n] (genV P A C))
      (genPhi P A C * idempotencyDefect^[n] (genV P A C))
      (idempotencyDefect^[n] (genV P A C)) =
    idempotencyDefect^[n] (genV P A C) +
      coneMinus P C * idempotencyDefect^[n] (genV P A C) := by
  have h11 : peirce11 P (idempotencyDefect^[n] (genV P A C)) =
      idempotencyDefect^[n] (qgtPlus P A C) := by
    unfold peirce11
    rw [genV_defect_iterates_left_projection hP A C n,
      qgtPlus_defect_iterates_right hP A C n]
  have h00 : peirce00 P (idempotencyDefect^[n] (genV P A C)) =
      idempotencyDefect^[n] (qgtMinus P A C) := by
    unfold peirce00
    rw [genV_defect_iterates_complement_left hP A C n,
      qgtMinus_defect_iterates_right hP A C n]
  have h01 : coneMinus P (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
      coneMinus P C * idempotencyDefect^[n] (genV P A C) := by
    have h1P : (1 - P) * coneMinus P C = coneMinus P C := by peirce_nf hP
    calc
      coneMinus P (genPhi P A C * idempotencyDefect^[n] (genV P A C)) =
        (1 - P) * ((genPhi P A C * idempotencyDefect^[n] (genV P A C)) * P) := by
        unfold coneMinus; noncomm_ring
      _ = (1 - P) * (coneMinus P C * idempotencyDefect^[n] (genV P A C)) := by
        rw [genPhi_defect_iterates_right hP A C n]
      _ = ((1 - P) * coneMinus P C) * idempotencyDefect^[n] (genV P A C) := by
        noncomm_ring
      _ = coneMinus P C * idempotencyDefect^[n] (genV P A C) := by
        rw [h1P]
  unfold blockLower
  rw [h11, h01, h00]
  calc
    idempotencyDefect^[n] (qgtPlus P A C) +
        coneMinus P C * idempotencyDefect^[n] (genV P A C) +
        idempotencyDefect^[n] (qgtMinus P A C) =
      (idempotencyDefect^[n] (qgtPlus P A C) +
          idempotencyDefect^[n] (qgtMinus P A C)) +
        coneMinus P C * idempotencyDefect^[n] (genV P A C) := by abel
    _ = idempotencyDefect^[n] (genV P A C) +
        coneMinus P C * idempotencyDefect^[n] (genV P A C) := by
      rw [← genV_defect_iterates_cycle_split hP A C n]

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

/-- Compression of the removed part to an orthogonal outer corner is zero.
Orthogonality is imposed on both sides; no commutativity is assumed. -/
theorem idempotentCompression_removed_orthogonal_corner (T : B) :
    P * (T - idempotentCompression Q T) * P = 0 := by
  have hPQ_compl : P * (1 - Q) = P := by
    calc
      P * (1 - Q) = P - P * Q := by noncomm_ring
      _ = P := by rw [hPQ]; simp
  have hCompl_P : (1 - Q) * P = P := by
    calc
      (1 - Q) * P = P - Q * P := by noncomm_ring
      _ = P := by rw [hQP]; simp
  unfold idempotentCompression
  calc
    P * (T - (1 - Q) * T * (1 - Q)) * P =
        P * T * P - (P * (1 - Q)) * T * ((1 - Q) * P) := by noncomm_ring
    _ = 0 := by rw [hPQ_compl, hCompl_P]; simp

end CornerPreservation

/-- Repeated complementary-corner interventions commute when their target
idempotents commute. -/
theorem idempotentCompression_comp_commute (Q R T : B)
    (hQR : Q * R = R * Q) :
    idempotentCompression Q (idempotentCompression R T) =
      idempotentCompression R (idempotentCompression Q T) := by
  have hcomp : (1 - Q) * (1 - R) = (1 - R) * (1 - Q) := by
    noncomm_ring [hQR]
  unfold idempotentCompression
  calc
    (1 - Q) * ((1 - R) * T * (1 - R)) * (1 - Q) =
        ((1 - Q) * (1 - R)) * T * ((1 - R) * (1 - Q)) := by noncomm_ring
    _ = ((1 - R) * (1 - Q)) * T * ((1 - Q) * (1 - R)) := by rw [hcomp]
    _ = (1 - R) * ((1 - Q) * T * (1 - Q)) * (1 - R) := by noncomm_ring

/-- The retained compression and removed part sum to the original operator. -/
theorem idempotentCompression_add_removed (Q T : B) :
    idempotentCompression Q T + (T - idempotentCompression Q T) = T := by
  abel

end InfoGeometry.OperatorAlgebra.PeirceSpine

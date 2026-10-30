/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Core.IdempotentGraphGrassmannian
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman

/-!
# Peirce transfer element and its defect recurrence

For an idempotent `P` and the existing Peirce generators, this file proves
polynomial identities for `T = P + Φ`. It does not identify this element with
the golden-mean shift adjacency operator: that separate carrier is owned by
`Omega.Graph.TransferMatrix` and a bridge would require an explicit homomorphism.
Likewise, the defect identities below do not assert a Galois extension.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The Peirce transfer element `P + Φ`. -/
def peirceTransfer (P A C : B) : B := P + genPhi P A C

/-- The complementary element `1 - P - Φ`. -/
def peirceTransferComplement (P A C : B) : B := (1 - P) - genPhi P A C

/-- The chiral variant `P + J`. -/
def peirceTransferJ (P A C : B) : B := P + genJ P A C

/-- A quadratic relation in an associative semiring yields a finite power
recurrence, with the coefficient on the left and no centrality assumption. -/
theorem quadratic_power_recurrence {R : Type*} [Semiring R]
    (x c : R) (h : x * x = x + c) (n : ℕ) :
    x ^ (n + 2) = x ^ (n + 1) + c * x ^ n := by
  calc
    x ^ (n + 2) = x ^ (2 + n) := by congr 1; omega
    _ = x ^ 2 * x ^ n := by rw [pow_add]
    _ = (x + c) * x ^ n := by rw [show x ^ 2 = x * x by simp [pow_succ], h]
    _ = x * x ^ n + c * x ^ n := by rw [add_mul]
    _ = x ^ (n + 1) + c * x ^ n := by
      congr 1
      rw [show n + 1 = 1 + n by omega, pow_add]
      simp

variable {P : B} (hP : P * P = P)
include hP

/-- The quadratic defect readouts and ordered Vieta products for the Peirce
transfer element. All products are in the arbitrary ambient associative ring. -/
theorem peirceTransfer_defect_and_vieta (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (peirceTransfer P A C) = genV P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (peirceTransferComplement P A C) = genV P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (peirceTransferJ P A C) = -genV P A C ∧
    peirceTransfer P A C + peirceTransferComplement P A C = 1 ∧
    peirceTransfer P A C * peirceTransferComplement P A C = -genV P A C ∧
    peirceTransferComplement P A C * peirceTransfer P A C = -genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [peirceTransfer, peirceTransferComplement, peirceTransferJ,
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect]);
     peirce_nf hP)

/-- The transfer element satisfies `T² = T + V`. This is the precise
operator-valued quadratic relation arising from the Peirce multiplication. -/
theorem peirceTransfer_quadratic_relation (A C : B) :
    peirceTransfer P A C * peirceTransfer P A C =
      peirceTransfer P A C + genV P A C := by
  simp only [peirceTransfer]
  peirce_nf hP

/-- The Peirce transfer powers obey the exact left-coefficient recurrence
`T^(n+2) = T^(n+1) + V*T^n` for every finite `n`. -/
theorem peirceTransfer_power_recurrence (A C : B) (n : ℕ) :
    peirceTransfer P A C ^ (n + 2) =
      peirceTransfer P A C ^ (n + 1) +
        genV P A C * peirceTransfer P A C ^ n :=
  quadratic_power_recurrence (x := peirceTransfer P A C)
    (c := genV P A C) (peirceTransfer_quadratic_relation hP A C) n

/-- The Peirce mass commutes with the transfer element. This is an identity
inside the generated Peirce algebra, not a claim that it is central in `B`. -/
theorem genV_commute_peirceTransfer (A C : B) :
    comm (genV P A C) (peirceTransfer P A C) = 0 := by
  simp only [peirceTransfer]
  peirce_nf hP

/-- The defect values of the two signs of the odd Peirce generator. -/
theorem genPhi_defect_pair (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genPhi P A C) = genV P A C - genPhi P A C ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (-genPhi P A C) = genV P A C + genPhi P A C := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect];
     peirce_nf hP)

/-- Applying the universal defect tower identity to `Φ`, and then using
`Φ² = V`, identifies the ordered product of the two defect values with `δ(V)`.
This is an element identity; it does not assert a Galois extension. -/
theorem genPhi_defect_product (A C : B) :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (-genPhi P A C) *
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genPhi P A C) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genV P A C) ∧
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genPhi P A C) *
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (-genPhi P A C) =
      InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genV P A C) := by
  have hΦ := archetype_A3_nilpotent_cones_and_tetraktys_table hP A C
  constructor
  · rw [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_neg_mul,
      hΦ.2.2.1]
  · rw [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_mul_neg,
      hΦ.2.2.1]

/-- Correct ordered product for the proposed chiral Mangoldt polynomial.
The factor involving `Σ` cannot in general be dropped: the right-hand side
retains it as `(1 + V) * (Σ - V²)`. -/
theorem chiral_mangoldt_product (A C : B) :
    (1 - genSig P A C) *
        (genSig P A C + genV P A C * genSig P A C) =
      (1 + genV P A C) *
        (genSig P A C - genV P A C * genV P A C) := by
  peirce_nf hP

/-- Exact correction to the tempting but generally false chiral Mangoldt
formula.  The missing term is twice the square of the lower Peirce cycle. -/
theorem chiral_mangoldt_claim_correction (A C : B) :
    (1 - genSig P A C) *
        (genSig P A C + genV P A C * genSig P A C) +
      (2 : ℤ) • ((coneMinus P C * conePlus P A) *
        (coneMinus P C * conePlus P A)) =
    genSig P A C - genV P A C * genV P A C -
      genV P A C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
        (genV P A C) := by
  simp only [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect]
  peirce_nf hP

/-- The proposed shortened chiral Mangoldt identity holds exactly when the
twice-scaled square of the lower Peirce cycle vanishes. -/
theorem chiral_mangoldt_claim_iff_lower_cycle_square (A C : B) :
    (1 - genSig P A C) *
        (genSig P A C + genV P A C * genSig P A C) =
      genSig P A C - genV P A C * genV P A C -
        genV P A C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
          (genV P A C) ↔
      (2 : ℤ) • ((coneMinus P C * conePlus P A) *
        (coneMinus P C * conePlus P A)) = 0 := by
  constructor
  · intro h
    have hc := chiral_mangoldt_claim_correction hP A C
    rw [h] at hc
    calc
      (2 : ℤ) • ((coneMinus P C * conePlus P A) *
          (coneMinus P C * conePlus P A)) =
          ((genSig P A C - genV P A C * genV P A C -
            genV P A C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
              (genV P A C)) + (2 : ℤ) • ((coneMinus P C * conePlus P A) *
            (coneMinus P C * conePlus P A))) -
          (genSig P A C - genV P A C * genV P A C -
            genV P A C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
              (genV P A C)) := by noncomm_ring
      _ = (genSig P A C - genV P A C * genV P A C -
          genV P A C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
            (genV P A C)) -
          (genSig P A C - genV P A C * genV P A C -
            genV P A C * InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
              (genV P A C)) := by rw [hc]
      _ = 0 := sub_self _
  · intro h
    have hc := chiral_mangoldt_claim_correction hP A C
    rw [h, add_zero] at hc
    exact hc

end InfoGeometry.OperatorAlgebra.PeirceSpine

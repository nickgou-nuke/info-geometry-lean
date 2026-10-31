/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectParity
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent

/-!
# Peirce boundary contribution to the idempotency defect

The statements below use the existing Peirce spine owners.  They express a
ring identity in an arbitrary associative, potentially noncommutative ring;
they do not identify this boundary term with analytic flux or tensor
separability.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceDefectBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The square of the odd Peirce component is the two-sided boundary
contraction (the `genV` operator with both inputs equal to `X`). -/
theorem oddGrade_square_eq_genV (P X : B) (hP : P * P = P) :
    oddGrade P X * oddGrade P X = genV P X X := by
  simp only [oddGrade, genV, anticomm, conePlus, coneMinus]
  peirce_nf hP

/-- Pinching the idempotency defect and taking the defect after pinching
differ by exactly the boundary quadratic term. The sign follows the convention
`idempotencyDefect X = X * X - X`. -/
theorem even_idempotencyDefect_sub (P X : B) (hP : P * P = P) :
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) =
      genV P X X := by
  rw [even_idempotencyDefect hP X, oddGrade_square_eq_genV P X hP]
  noncomm_ring

/-- If `X` is idempotent, its Peirce pinching has defect equal to the negative
boundary quadratic term. -/
theorem idempotencyDefect_evenGrade_of_idempotent
    (P X : B) (hP : P * P = P) (hX : X * X = X) :
    idempotencyDefect (evenGrade P X) = -genV P X X := by
  have h := even_idempotencyDefect_sub P X hP
  have hXdef : idempotencyDefect X = 0 := by
    simp [idempotencyDefect, hX]
  rw [hXdef] at h
  simp only [evenGrade, zero_mul, mul_zero, add_zero, zero_sub] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Pinched upper-corner defect minus the upper-corner defect of the input is
the upper Peirce cycle `qgtPlus P X X`. -/
theorem peirce11_idempotencyDefect_sub (P X : B) (hP : P * P = P) :
    peirce11 P (idempotencyDefect X) - idempotencyDefect (peirce11 P X) =
      qgtPlus P X X := by
  simp only [idempotencyDefect, qgtPlus, conePlus, coneMinus]
  peirce_nf hP

/-- Pinched lower-corner defect minus the lower-corner defect of the input is
the lower Peirce cycle `qgtMinus P X X`. -/
theorem peirce00_idempotencyDefect_sub (P X : B) (hP : P * P = P) :
    peirce00 P (idempotencyDefect X) - idempotencyDefect (peirce00 P X) =
      qgtMinus P X X := by
  simp only [idempotencyDefect, qgtMinus, conePlus, coneMinus]
  peirce_nf hP

/-- For an idempotent `X`, the upper-corner compression `P X P` has idempotency
defect equal to `-qgtPlus P X X`. -/
theorem idempotencyDefect_peirce11_of_idempotent
    (P X : B) (hP : P * P = P) (hX : X * X = X) :
    idempotencyDefect (peirce11 P X) = -qgtPlus P X X := by
  have h := peirce11_idempotencyDefect_sub P X hP
  have hXdef : idempotencyDefect X = 0 := by
    simp [idempotencyDefect, hX]
  rw [hXdef] at h
  simp only [peirce11, zero_mul, mul_zero, zero_sub] at h
  exact neg_eq_iff_eq_neg.mp h

/-- For an idempotent `X`, the lower-corner compression `(1 - P) X (1 - P)` has
idempotency defect equal to `-qgtMinus P X X`. -/
theorem idempotencyDefect_peirce00_of_idempotent
    (P X : B) (hP : P * P = P) (hX : X * X = X) :
    idempotencyDefect (peirce00 P X) = -qgtMinus P X X := by
  have h := peirce00_idempotencyDefect_sub P X hP
  have hXdef : idempotencyDefect X = 0 := by
    simp [idempotencyDefect, hX]
  rw [hXdef] at h
  simp only [peirce00, zero_mul, mul_zero, zero_sub] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Upper-corner projection of `genV` extracts the upper Peirce cycle `qgtPlus`. -/
theorem peirce11_genV_eq_qgtPlus (P A C : B) (hP : P * P = P) :
    peirce11 P (genV P A C) = qgtPlus P A C := by
  simp only [qgtPlus]
  peirce_nf hP

/-- Lower-corner projection of `genV` extracts the lower Peirce cycle `qgtMinus`. -/
theorem peirce00_genV_eq_qgtMinus (P A C : B) (hP : P * P = P) :
    peirce00 P (genV P A C) = qgtMinus P A C := by
  simp only [qgtMinus]
  peirce_nf hP

/-- The boundary quadratic term `genV P A C` vanishes if and only if both of
its Peirce corner cycles vanish. -/
theorem genV_eq_zero_iff_qgt_zero (P A C : B) (hP : P * P = P) :
    genV P A C = 0 ↔ qgtPlus P A C = 0 ∧ qgtMinus P A C = 0 := by
  constructor
  · intro hV
    have h11 := peirce11_genV_eq_qgtPlus P A C hP
    have h00 := peirce00_genV_eq_qgtMinus P A C hP
    rw [hV] at h11 h00
    simp only [peirce11, peirce00, mul_zero, zero_mul] at h11 h00
    exact ⟨h11.symm, h00.symm⟩
  · rintro ⟨h1, h2⟩
    change qgtPlus P A C + qgtMinus P A C = 0
    rw [h1, h2, add_zero]

/-- Every stage of the unipotent tower satisfies the pinching–defect identity;
the associated Bruhat conjugation fixes the boundary metric. -/
theorem unipotentIdempotentTower_defect_and_bruhat_fix
    (A : ℕ → B) (P X : B) (hP : P * P = P) (k : ℕ) :
    let Pk := unipotentIdempotentTower A k P
    evenGrade Pk (idempotencyDefect X) - idempotencyDefect (evenGrade Pk X) =
      genV Pk X X ∧
    chartBruhatConj Pk X X (genV Pk X X) = genV Pk X X := by
  intro Pk
  have hPk : Pk * Pk = Pk := unipotentIdempotentTower_idempotent hP A k
  exact ⟨even_idempotencyDefect_sub Pk X hPk,
    chartBruhatConj_genV hPk X X⟩

end InfoGeometry.OperatorAlgebra.PeirceDefectBridge

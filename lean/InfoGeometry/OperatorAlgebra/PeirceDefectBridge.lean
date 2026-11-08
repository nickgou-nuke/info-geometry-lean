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

/-! ## 2. Peirce Non-Abelian Maurer–Cartan Curvature, Covariant Derivative & Self-Dual Yang–Mills -/

/-- **Peirce Inner Grading Derivation (`peirceGradingDeriv`)**:
In any associative ring `B`, `d_P(X) = [P, X] = P * X - X * P = genJ P X X`. -/
def peirceGradingDeriv (P X : B) : B :=
  PeirceSpine.comm P X

/-- The inner Peirce map is a genuine Leibniz derivation on the underlying
noncommutative ring. This is the ungraded algebraic derivation; the exterior
graded differential is represented separately by `ExteriorDifferentialData`. -/
theorem peirceGradingDeriv_leibniz (P X Y : B) :
    peirceGradingDeriv P (X * Y) =
      peirceGradingDeriv P X * Y + X * peirceGradingDeriv P Y := by
  unfold peirceGradingDeriv PeirceSpine.comm
  noncomm_ring

/-- **Peirce Non-Abelian Covariant Derivative (`peirceCovariantDeriv`)**:
With Peirce grading derivation `d_P = [P, ·]` and off-diagonal chiral connection
`A_conn = genPhi P A C = N₊ + N₋`, acts on `X : B` by `d_P(X) + [genPhi P A C, X]`. -/
def peirceCovariantDeriv (P A C X : B) : B :=
  peirceGradingDeriv P X + PeirceSpine.comm (genPhi P A C) X

/-- **Peirce Maurer–Cartan Curvature (`peirceMaurerCartanCurvature`)**:
The Maurer–Cartan curvature `F_P(A, C) = d_P(genPhi P A C) + (genPhi P A C)²` of the
off-diagonal Peirce connection `genPhi P A C`. -/
def peirceMaurerCartanCurvature (P A C : B) : B :=
  peirceGradingDeriv P (genPhi P A C) + genPhi P A C * genPhi P A C

/-- **Peirce Maurer–Cartan Curvature Decomposition, Covariant Bianchi & Self-Dual Yang–Mills**:
For any idempotent `P` (`P * P = P`) and any `A, C, X, Y : B` in an associative ring `B`:
1. **Leibniz Rule & Nilpotency on Even Sector:**
   `peirceGradingDeriv P (X * Y) = peirceGradingDeriv P X * Y + X * peirceGradingDeriv P Y`
   and `peirceGradingDeriv P (evenGrade P X) = 0`;
2. **Exact Maurer–Cartan Decomposition into Even (`genV`) and Odd (`genJ`) Curvature:**
   `peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C`, with
   `evenGrade P (peirceMaurerCartanCurvature P A C) = genV P A C` and
   `oddGrade P (peirceMaurerCartanCurvature P A C) = genJ P A C`;
3. **Self-Duality / Anti-Self-Duality under the Peirce Hodge-Parity Star `parityConj P`:**
   `parityConj P (genV P A C) = genV P A C` (even curvature is self-dual) and
   `parityConj P (genJ P A C) = -genJ P A C` (odd curvature is anti-self-dual);
4. **Covariant Bianchi & Vacuum Self-Dual Yang–Mills Identity for `genV P A C`:**
   Both the grading derivation and connection commutator vanish on `genV P A C`:
   `peirceGradingDeriv P (genV P A C) = 0`, `PeirceSpine.comm (genPhi P A C) (genV P A C) = 0`,
   `peirceCovariantDeriv P A C (genV P A C) = 0`, and
   `peirceCovariantDeriv P A C (parityConj P (genV P A C)) = 0`. -/
theorem peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills
    {P : B} (hP : P * P = P) (A C X Y : B) :
    peirceGradingDeriv P (X * Y) =
      peirceGradingDeriv P X * Y + X * peirceGradingDeriv P Y ∧
    peirceGradingDeriv P (evenGrade P X) = 0 ∧
    peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
    evenGrade P (peirceMaurerCartanCurvature P A C) = genV P A C ∧
    oddGrade P (peirceMaurerCartanCurvature P A C) = genJ P A C ∧
    parityConj P (genV P A C) = genV P A C ∧
    parityConj P (genJ P A C) = -genJ P A C ∧
    peirceGradingDeriv P (genV P A C) = 0 ∧
    PeirceSpine.comm (genPhi P A C) (genV P A C) = 0 ∧
    peirceCovariantDeriv P A C (genV P A C) = 0 ∧
    peirceCovariantDeriv P A C (parityConj P (genV P A C)) = 0 := by
  have hSD : parityConj P (genV P A C) = genV P A C := by
    unfold parityConj; peirce_nf hP
  have hCovV : peirceCovariantDeriv P A C (genV P A C) = 0 := by
    unfold peirceCovariantDeriv peirceGradingDeriv
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_, hSD, ?_, ?_, ?_, hCovV, ?_⟩
  · unfold peirceGradingDeriv PeirceSpine.comm; noncomm_ring
  · unfold peirceGradingDeriv; peirce_nf hP
  · unfold peirceMaurerCartanCurvature peirceGradingDeriv; peirce_nf hP
  · unfold peirceMaurerCartanCurvature peirceGradingDeriv; peirce_nf hP
  · unfold peirceMaurerCartanCurvature peirceGradingDeriv; peirce_nf hP
  · unfold parityConj; peirce_nf hP
  · unfold peirceGradingDeriv; peirce_nf hP
  · peirce_nf hP
  · rw [hSD, hCovV]

end InfoGeometry.OperatorAlgebra.PeirceDefectBridge

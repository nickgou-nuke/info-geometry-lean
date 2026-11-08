/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.GolayLeechMOGSheetPoset

/-!
# Selected cross-grade commutators of the five Kantor–Peirce operators

These are explicit computations in an associative operator ring. The
superoperator commutators land in the indicated charge sectors. This file
formalizes the four displayed brackets; it does not assert the uncomputed
full bracket table.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Left multiplication by an idempotent is idempotent as an operator. -/
private lemma P_assoc {P : B} (hP : P * P = P) (X : B) :
    P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

/-- Commutator of two endomorphisms, evaluated at an operator. -/
def kantorSuperComm (F G : B → B) (X : B) : B := F (G X) - G (F X)

/-- Jacobi identity for pointwise commutators of subtraction-preserving maps.
The additivity hypotheses are explicit because `B → B` alone carries no
linearity structure. -/
theorem kantorSuperComm_jacobi_of_sub
    (F G H : B → B)
    (hF : ∀ x y, F (x - y) = F x - F y)
    (hG : ∀ x y, G (x - y) = G x - G y)
    (hH : ∀ x y, H (x - y) = H x - H y)
    (X : B) :
    kantorSuperComm F (fun Y => kantorSuperComm G H Y) X +
      kantorSuperComm G (fun Y => kantorSuperComm H F Y) X +
      kantorSuperComm H (fun Y => kantorSuperComm F G Y) X = 0 := by
  dsimp [kantorSuperComm]
  simp only [hF, hG, hH]
  abel

/-- Jacobi identity for the mixed `(+1,-1,-2)` Kantor triple, including the
cross-grade bracket from the A₅₄ table. -/
theorem kantor_cross_grade_jacobi
    {P : B} (A C X : B) :
    kantorSuperComm (kantorGp1 P A)
        (fun Y => kantorSuperComm (kantorGm1 P C) (kantorGm2 P C) Y) X +
      kantorSuperComm (kantorGm1 P C)
        (fun Y => kantorSuperComm (kantorGm2 P C) (kantorGp1 P A) Y) X +
      kantorSuperComm (kantorGm2 P C)
        (fun Y => kantorSuperComm (kantorGp1 P A) (kantorGm1 P C) Y) X = 0 := by
  apply kantorSuperComm_jacobi_of_sub
  · intro x y
    dsimp [kantorGp1, comm]
    noncomm_ring
  · intro x y
    dsimp [kantorGm1, comm]
    noncomm_ring
  · intro x y
    dsimp [kantorGm2]
    noncomm_ring

/-- Four explicit positive/negative Kantor grade brackets and the charge of
each result. -/
theorem kantor_cross_grade_brackets
    {P : B} (hP : P * P = P) (A C X : B) :
    kantorSuperComm (kantorGp1 P A) (kantorGm1 P C) X =
      comm (genSig P A C) X ∧
    kantorSuperComm (kantorGp1 P A) (kantorGm2 P C) X =
      kantorTriple (genSig P A C) X (coneMinus P C) ∧
    superChargeP (kantorSuperComm (kantorGp1 P A) (kantorGm2 P C)) P X =
      -kantorSuperComm (kantorGp1 P A) (kantorGm2 P C) X ∧
    kantorSuperComm (kantorGm1 P C) (kantorGp2 P A) X =
      -kantorTriple (genSig P A C) X (conePlus P A) ∧
    superChargeP (kantorSuperComm (kantorGm1 P C) (kantorGp2 P A)) P X =
      kantorSuperComm (kantorGm1 P C) (kantorGp2 P A) X ∧
    kantorSuperComm (kantorGp2 P A) (kantorGm2 P C) X =
      qgtPlus P A C * X * qgtMinus P A C -
        qgtMinus P A C * X * qgtPlus P A C ∧
    superChargeP (kantorSuperComm (kantorGp2 P A) (kantorGm2 P C)) P X = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change kantorGp1 P A (kantorGm1 P C X) -
      kantorGm1 P C (kantorGp1 P A X) = comm (genSig P A C) X
    peirce_abel_golay hP
  · change kantorGp1 P A (kantorGm2 P C X) -
      kantorGm2 P C (kantorGp1 P A X) =
        kantorTriple (genSig P A C) X (coneMinus P C)
    peirce_abel_golay hP
  · change superChargeP
      (fun Y => kantorGp1 P A (kantorGm2 P C Y) -
        kantorGm2 P C (kantorGp1 P A Y)) P X =
      -(kantorGp1 P A (kantorGm2 P C X) -
        kantorGm2 P C (kantorGp1 P A X))
    unfold superChargeP
    peirce_abel_golay hP
  · change kantorGm1 P C (kantorGp2 P A X) -
      kantorGp2 P A (kantorGm1 P C X) =
        -kantorTriple (genSig P A C) X (conePlus P A)
    peirce_abel_golay hP
  · change superChargeP
      (fun Y => kantorGm1 P C (kantorGp2 P A Y) -
        kantorGp2 P A (kantorGm1 P C Y)) P X =
      kantorGm1 P C (kantorGp2 P A X) -
        kantorGp2 P A (kantorGm1 P C X)
    unfold superChargeP
    peirce_abel_golay hP
  · change kantorGp2 P A (kantorGm2 P C X) -
      kantorGm2 P C (kantorGp2 P A X) =
        qgtPlus P A C * X * qgtMinus P A C -
          qgtMinus P A C * X * qgtPlus P A C
    peirce_abel_golay hP
  · change superChargeP
      (fun Y => kantorGp2 P A (kantorGm2 P C Y) -
        kantorGm2 P C (kantorGp2 P A Y)) P X = 0
    unfold superChargeP
    peirce_abel_golay hP

/-- Endpoint values of the two mixed grade brackets.  They vanish on the
unit; on the corresponding Peirce corners their values have opposite signs.
In particular, the two corner values are not both `V * Σ`.
-/
theorem kantor_cross_grade_brackets_on_unit_and_corners
    {P : B} (hP : P * P = P) (A C : B) :
    kantorSuperComm (kantorGp1 P A) (kantorGm2 P C) 1 = 0 ∧
    kantorSuperComm (kantorGm1 P C) (kantorGp2 P A) 1 = 0 ∧
    kantorSuperComm (kantorGp1 P A) (kantorGm2 P C) (conePlus P A) =
      genV P A C * genSig P A C ∧
    kantorSuperComm (kantorGm1 P C) (kantorGp2 P A) (coneMinus P C) =
      -(genV P A C * genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change kantorGp1 P A (kantorGm2 P C 1) -
      kantorGm2 P C (kantorGp1 P A 1) = 0
    peirce_abel_golay hP
  · change kantorGm1 P C (kantorGp2 P A 1) -
      kantorGp2 P A (kantorGm1 P C 1) = 0
    peirce_abel_golay hP
  · calc
      kantorSuperComm (kantorGp1 P A) (kantorGm2 P C) (conePlus P A) =
          kantorTriple (genSig P A C) (conePlus P A) (coneMinus P C) :=
        (kantor_cross_grade_brackets hP A C (conePlus P A)).2.1
      _ = genV P A C * genSig P A C := by
        dsimp [kantorTriple]
        peirce_nf hP
  · calc
      kantorSuperComm (kantorGm1 P C) (kantorGp2 P A) (coneMinus P C) =
          -kantorTriple (genSig P A C) (coneMinus P C) (conePlus P A) :=
        (kantor_cross_grade_brackets hP A C (coneMinus P C)).2.2.2.1
      _ = -(genV P A C * genSig P A C) := by
        dsimp [kantorTriple]
        peirce_nf hP

/-- The two extremal Kantor sandwiches round-trip the opposite transition
cone by the square of the shared Peirce metric.  These are the ordered
`G_{+2} G_{-2}` and `G_{-2} G_{+2}` actions from the A51 ladder. -/
theorem kantor_extremal_roundtrip_on_transition_cones
    {P : B} (hP : P * P = P) (A C : B) :
    kantorGp2 P A (kantorGm2 P C (conePlus P A)) =
      (genV P A C * genV P A C) * conePlus P A ∧
    kantorGm2 P C (kantorGp2 P A (coneMinus P C)) =
      (genV P A C * genV P A C) * coneMinus P C := by
  constructor <;> peirce_abel_golay hP

/-- Same-sign Kantor grades have no further extremal square, while the
charge-one commutator squares land in the corresponding charge-two sector.
This records the A52 boundary of the five-grade ladder. -/
theorem kantor_same_sign_extremal_closure
    {P : B} (hP : P * P = P) (A C X : B) :
    kantorGp1 P A (kantorGp2 P A X) -
        kantorGp2 P A (kantorGp1 P A X) = 0 ∧
    kantorGm1 P C (kantorGm2 P C X) -
        kantorGm2 P C (kantorGm1 P C X) = 0 ∧
    kantorGp2 P A (kantorGp2 P A X) = 0 ∧
    kantorGm2 P C (kantorGm2 P C X) = 0 ∧
    kantorGp1 P A (kantorGp1 P A X) =
      -((2 : ℤ) • kantorGp2 P A X) ∧
    kantorGm1 P C (kantorGm1 P C X) =
      -((2 : ℤ) • kantorGm2 P C X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_abel_golay hP

/-- The chiral difference of the two Peirce corners acts with opposite signs
on the two transition cones. -/
theorem kantor_chiral_absorption_on_transition_cones
    {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * conePlus P A = genV P A C * conePlus P A ∧
    conePlus P A * genSig P A C = -(genV P A C * conePlus P A) ∧
    genSig P A C * coneMinus P C = -(genV P A C * coneMinus P C) ∧
    coneMinus P C * genSig P A C = genV P A C * coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- The extremal same-cone sandwiches see the odd Peirce grade, whereas the
charge-zero mixed sandwich sees only the even grade. This records the correct
block separation for the five Kantor operators. -/
theorem kantor_peirce_even_odd_grade_separation
    {P : B} (hP : P * P = P) (A C X : B) :
    kantorGp2 P A X + kantorGm2 P C X =
      conePlus P A * oddGrade P X * conePlus P A +
        coneMinus P C * oddGrade P X * coneMinus P C ∧
    kantorG0 P A C (evenGrade P X) = kantorG0 P A C X ∧
    kantorG0 P A C (oddGrade P X) = 0 ∧
    kantorGp2 P A (evenGrade P X) + kantorGm2 P C (evenGrade P X) = 0 ∧
    kantorGp2 P A (oddGrade P X) + kantorGm2 P C (oddGrade P X) =
      kantorGp2 P A X + kantorGm2 P C X ∧
    (kantorGp2 P A (kantorGm2 P C X) +
      kantorGm2 P C (kantorGp2 P A X)) =
      qgtPlus P A C * X * qgtMinus P A C +
        qgtMinus P A C * X * qgtPlus P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try dsimp only [evenGrade, oddGrade]) <;> peirce_abel_golay hP

/-- The opposite-cone compositions and the zero-grade square separate the
odd and even Peirce supports, respectively. -/
theorem kantor_composition_even_odd_support
    {P : B} (hP : P * P = P) (A C X : B) :
    kantorGp2 P A (kantorGm2 P C X) +
        kantorGm2 P C (kantorGp2 P A X) =
      qgtPlus P A C * oddGrade P X * qgtMinus P A C +
        qgtMinus P A C * oddGrade P X * qgtPlus P A C ∧
    kantorGp2 P A (kantorGm2 P C (evenGrade P X)) +
        kantorGm2 P C (kantorGp2 P A (evenGrade P X)) = 0 ∧
    kantorG0 P A C (kantorG0 P A C X) =
      qgtPlus P A C * evenGrade P X * qgtPlus P A C +
        qgtMinus P A C * evenGrade P X * qgtMinus P A C ∧
    kantorG0 P A C (kantorG0 P A C (oddGrade P X)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (try dsimp only [evenGrade, oddGrade]) <;> peirce_abel_golay hP

end InfoGeometry.OperatorAlgebra.PeirceSpine

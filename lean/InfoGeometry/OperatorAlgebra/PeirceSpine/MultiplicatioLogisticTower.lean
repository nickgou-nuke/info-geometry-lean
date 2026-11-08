/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import Mathlib.Tactic.NoncommRing

/-!
# D₄₇: finite-depth defect and logistic-stone identities

This module reuses the Peirce defect-iteration and homogenized-channel owners.
It formalizes finite iterates in an arbitrary ring; no analytic or infinite-limit
claim is made. The mandala maps are additive channels, not idempotent
endomorphisms of the ambient ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The metric at depth `n`, obtained by iterating the idempotency defect on
both orthogonal Peirce cycles. -/
def multiplicatioMetric (n : ℕ) (P A C : B) : B :=
  idempotencyDefect^[n] (qgtPlus P A C) +
    idempotencyDefect^[n] (qgtMinus P A C)

/-- The signed difference of the two depth-`n` Peirce sheets. -/
def multiplicatioCurvature (n : ℕ) (P A C : B) : B :=
  idempotencyDefect^[n] (qgtPlus P A C) -
    idempotencyDefect^[n] (qgtMinus P A C)

/-- The depth-`n` logistic stone `P - Σₙ`. -/
def multiplicatioStone (n : ℕ) (P A C : B) : B :=
  P - multiplicatioCurvature n P A C

/-- The centered, integer-scaled radical of a depth-`n` stone. -/
def multiplicatioRadical (n : ℕ) (P A C : B) : B :=
  (2 : ℤ) • multiplicatioStone n P A C - 1

/-- The metric tower is exactly the iterated defect of the original metric. -/
theorem multiplicatioMetric_eq_iterated_genV {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    multiplicatioMetric n P A C = idempotencyDefect^[n] (genV P A C) := by
  exact (genV_defect_iterates_cycle_split hP A C n).symm

/-- One more metric step is the idempotency defect of the current metric. -/
theorem multiplicatioMetric_succ_eq_defect {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    multiplicatioMetric (n + 1) P A C =
      idempotencyDefect (multiplicatioMetric n P A C) := by
  rw [multiplicatioMetric_eq_iterated_genV hP A C (n + 1),
    multiplicatioMetric_eq_iterated_genV hP A C n]
  simp only [Function.iterate_succ_apply']

/-- A general chiral defect formula. It requires only that `P` is idempotent
and that the chiral element commutes with `P`. -/
theorem idempotencyDefect_sub_commuting {P S : B}
    (hP : P * P = P) (hPS : P * S = S * P) :
    idempotencyDefect (P - S) = S * S - invS P * S := by
  unfold idempotencyDefect invS
  simp only [sub_mul, mul_sub, one_mul, hP, hPS]
  noncomm_ring

/-- If the chiral element has grading image `V` and square `V²`, then the
stone defect is the defect of `V`. -/
theorem idempotencyDefect_sub_chiral {P S V : B}
    (hP : P * P = P) (hPS : P * S = S * P)
    (hParity : invS P * S = V) (hSquare : S * S = V * V) :
    idempotencyDefect (P - S) = idempotencyDefect V := by
  rw [idempotencyDefect_sub_commuting hP hPS, hSquare, hParity]
  rfl

/-- Universal discriminant identity in a ring, with no commutation assumption. -/
theorem centered_square_eq_one_add_four_defect (x : B) :
    ((2 : ℤ) • x - 1) * ((2 : ℤ) • x - 1) =
      1 + (4 : ℤ) • idempotencyDefect x := by
  unfold idempotencyDefect
  noncomm_ring

/-- The depth-`n` chiral and metric sheets have the expected Peirce supports. -/
theorem multiplicatio_sheet_support {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    P * idempotencyDefect^[n] (qgtPlus P A C) =
        idempotencyDefect^[n] (qgtPlus P A C) ∧
    idempotencyDefect^[n] (qgtPlus P A C) * P =
        idempotencyDefect^[n] (qgtPlus P A C) ∧
    (1 - P) * idempotencyDefect^[n] (qgtMinus P A C) =
        idempotencyDefect^[n] (qgtMinus P A C) ∧
    idempotencyDefect^[n] (qgtMinus P A C) * (1 - P) =
        idempotencyDefect^[n] (qgtMinus P A C) := by
  exact ⟨qgtPlus_defect_iterates_left hP A C n,
    qgtPlus_defect_iterates_right hP A C n,
    qgtMinus_defect_iterates_left hP A C n,
    qgtMinus_defect_iterates_right hP A C n⟩

/-- The depth-`n` signed sheet is grading-dual to the depth-`n` metric. -/
theorem multiplicatio_parity_and_square {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    invS P * multiplicatioCurvature n P A C =
        multiplicatioMetric n P A C ∧
    multiplicatioCurvature n P A C * multiplicatioCurvature n P A C =
        multiplicatioMetric n P A C * multiplicatioMetric n P A C ∧
    P * multiplicatioCurvature n P A C =
        multiplicatioCurvature n P A C * P := by
  let X := idempotencyDefect^[n] (qgtPlus P A C)
  let Y := idempotencyDefect^[n] (qgtMinus P A C)
  have hXleft := qgtPlus_defect_iterates_left hP A C n
  have hXright := qgtPlus_defect_iterates_right hP A C n
  have hYleft := qgtMinus_defect_iterates_left hP A C n
  have hYright := qgtMinus_defect_iterates_right hP A C n
  have hXY := (qgt_defect_iterates_orthogonal hP A C n).1
  have hYX := (qgt_defect_iterates_orthogonal hP A C n).2
  change P * X = X at hXleft
  change X * P = X at hXright
  change (1 - P) * Y = Y at hYleft
  change Y * (1 - P) = Y at hYright
  change X * Y = 0 at hXY
  change Y * X = 0 at hYX
  have hPcomp : P * (1 - P) = 0 := by noncomm_ring [hP]
  have hcompP : (1 - P) * P = 0 := by noncomm_ring [hP]
  have hPY : P * Y = 0 := by
    calc
      P * Y = P * ((1 - P) * Y) := by rw [hYleft]
      _ = (P * (1 - P)) * Y := by rw [mul_assoc]
      _ = 0 := by rw [hPcomp, zero_mul]
  have hYP : Y * P = 0 := by
    calc
      Y * P = (Y * (1 - P)) * P := by rw [hYright]
      _ = Y * ((1 - P) * P) := by rw [mul_assoc]
      _ = 0 := by rw [hcompP, mul_zero]
  have hCompX : (1 - P) * X = 0 := by
    calc
      (1 - P) * X = (1 - P) * (P * X) := by rw [hXleft]
      _ = ((1 - P) * P) * X := by rw [mul_assoc]
      _ = 0 := by rw [hcompP, zero_mul]
  constructor
  · unfold invS multiplicatioCurvature multiplicatioMetric
    change (P - (1 - P)) * (X - Y) = X + Y
    simp only [sub_mul, mul_sub, hXleft, hPY, hCompX, hYleft]
    noncomm_ring
  constructor
  · unfold multiplicatioCurvature multiplicatioMetric
    change (X - Y) * (X - Y) = (X + Y) * (X + Y)
    calc
      (X - Y) * (X - Y) = X * X - X * Y - Y * X + Y * Y := by noncomm_ring
      _ = X * X + X * Y + Y * X + Y * Y := by rw [hXY, hYX]; noncomm_ring
      _ = (X + Y) * (X + Y) := by noncomm_ring
  · unfold multiplicatioCurvature
    change P * (X - Y) = (X - Y) * P
    rw [mul_sub, sub_mul, hXleft, hPY, hXright, hYP]

/-- The finite-depth logistic stone has defect exactly the next metric level. -/
theorem multiplicatio_stone_defect {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    idempotencyDefect (multiplicatioStone n P A C) =
      multiplicatioMetric (n + 1) P A C := by
  have hParity := (multiplicatio_parity_and_square hP A C n).1
  have hSquare := (multiplicatio_parity_and_square hP A C n).2.1
  have hComm : P * multiplicatioCurvature n P A C =
      multiplicatioCurvature n P A C * P :=
    (multiplicatio_parity_and_square hP A C n).2.2
  calc
    idempotencyDefect (multiplicatioStone n P A C) =
        idempotencyDefect (multiplicatioMetric n P A C) :=
      idempotencyDefect_sub_chiral hP hComm hParity hSquare
    _ = multiplicatioMetric (n + 1) P A C :=
      (multiplicatioMetric_succ_eq_defect hP A C n).symm

/-- Every finite-depth stone belongs to the diagonal Peirce subalgebra. -/
theorem multiplicatio_stone_commutes_with_P {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    comm P (multiplicatioStone n P A C) = 0 := by
  have hComm := (multiplicatio_parity_and_square hP A C n).2.2
  unfold comm multiplicatioStone
  rw [mul_sub, sub_mul, hP, hComm]
  noncomm_ring

/-- Every finite-depth stone also commutes with the original chiral element.
The proof uses that defect iterates are polynomials in their own sheet and
that the two Peirce sheets annihilate across the diagonal split. -/
theorem multiplicatio_stone_commutes_with_initial_curvature {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    comm (genSig P A C) (multiplicatioStone n P A C) = 0 := by
  let Qp := qgtPlus P A C
  let Qm := qgtMinus P A C
  let X := idempotencyDefect^[n] Qp
  let Y := idempotencyDefect^[n] Qm
  have hPxp : P * X = X := qgtPlus_defect_iterates_left hP A C n
  have hXpp : X * P = X := qgtPlus_defect_iterates_right hP A C n
  have hYcomp : (1 - P) * Y = Y := qgtMinus_defect_iterates_left hP A C n
  have hYcompR : Y * (1 - P) = Y := qgtMinus_defect_iterates_right hP A C n
  change P * X = X at hPxp
  change X * P = X at hXpp
  change (1 - P) * Y = Y at hYcomp
  change Y * (1 - P) = Y at hYcompR
  have hPY : P * Y = 0 := by
    rw [← hYcomp]
    peirce_nf hP
  have hYP : Y * P = 0 := by
    rw [← hYcompR]
    peirce_nf hP
  have hCompX : (1 - P) * X = 0 := by
    rw [← hPxp]
    peirce_nf hP
  have hQpP : Qp * P = Qp := by
    dsimp [Qp, qgtPlus]
    peirce_nf hP
  have hQmComp : Qm * (1 - P) = Qm := by
    dsimp [Qm, qgtMinus]
    peirce_nf hP
  have hPq : P * Qp = Qp := by
    dsimp [Qp, qgtPlus]
    peirce_nf hP
  have hQmP : Qm * P = 0 := by
    dsimp [Qm, qgtMinus]
    peirce_nf hP
  have hPQm : P * Qm = 0 := by
    dsimp [Qm, qgtMinus]
    peirce_nf hP
  have hQpY : Qp * Y = 0 := by
    calc
      Qp * Y = (Qp * P) * Y := by rw [hQpP]
      _ = Qp * (P * Y) := by simp only [mul_assoc]
      _ = 0 := by rw [hPY, mul_zero]
  have hYQp : Y * Qp = 0 := by
    calc
      Y * Qp = Y * (P * Qp) := by rw [hPq]
      _ = (Y * P) * Qp := by rw [mul_assoc]
      _ = 0 := by rw [hYP, zero_mul]
  have hQmX : Qm * X = 0 := by
    calc
      Qm * X = (Qm * (1 - P)) * X := by rw [hQmComp]
      _ = Qm * ((1 - P) * X) := by simp only [mul_assoc]
      _ = 0 := by rw [hCompX, mul_zero]
  have hXQm : X * Qm = 0 := by
    calc
      X * Qm = (X * P) * Qm := by rw [hXpp]
      _ = X * (P * Qm) := by simp only [mul_assoc]
      _ = 0 := by rw [hPQm, mul_zero]
  have hSameP : X * Qp = Qp * X := by
    exact (idempotencyDefect_iterates_intertwines (x := Qp) (y := Qp)
      (z := Qp) rfl n)
  have hSameM : Y * Qm = Qm * Y := by
    exact (idempotencyDefect_iterates_intertwines (x := Qm) (y := Qm)
      (z := Qm) rfl n)
  change (Qp - Qm) * (P - (X - Y)) -
      (P - (X - Y)) * (Qp - Qm) = 0
  noncomm_ring [hQpP, hPq, hQmP, hPQm, hPY, hYP, hCompX,
    hQpY, hYQp, hQmX, hXQm, hSameP, hSameM]

/-- Stones at any two finite depths commute with each other. Same-sheet
defect iterates commute because they are polynomials in the same cycle;
opposite sheets annihilate because they remain in complementary Peirce
corners. -/
theorem multiplicatio_stones_pairwise_commute {P : B}
    (hP : P * P = P) (A C : B) (n m : ℕ) :
    comm (multiplicatioStone n P A C) (multiplicatioStone m P A C) = 0 := by
  let Xn := idempotencyDefect^[n] (qgtPlus P A C)
  let Yn := idempotencyDefect^[n] (qgtMinus P A C)
  let Xm := idempotencyDefect^[m] (qgtPlus P A C)
  let Ym := idempotencyDefect^[m] (qgtMinus P A C)
  have hXnP : Xn * P = Xn := by
    exact qgtPlus_defect_iterates_right hP A C n
  have hXmP : Xm * P = Xm := by
    exact qgtPlus_defect_iterates_right hP A C m
  have hPYmSheet : (1 - P) * Ym = Ym := by
    exact qgtMinus_defect_iterates_left hP A C m
  have hYnComp : Yn * (1 - P) = Yn := by
    exact qgtMinus_defect_iterates_right hP A C n
  have hYmComp : Ym * (1 - P) = Ym := by
    exact qgtMinus_defect_iterates_right hP A C m
  have hCompP : (1 - P) * P = 0 := by noncomm_ring [hP]
  have hPComp : P * (1 - P) = 0 := by noncomm_ring [hP]
  have hPYm : P * Ym = 0 := by
    calc
      P * Ym = P * ((1 - P) * Ym) := by rw [hPYmSheet]
      _ = (P * (1 - P)) * Ym := by rw [mul_assoc]
      _ = 0 := by rw [hPComp, zero_mul]
  have hXnLeft : P * Xn = Xn := qgtPlus_defect_iterates_left hP A C n
  have hXmLeft : P * Xm = Xm := qgtPlus_defect_iterates_left hP A C m
  have hCompXn : (1 - P) * Xn = 0 := by
    calc
      (1 - P) * Xn = (1 - P) * (P * Xn) := by rw [hXnLeft]
      _ = ((1 - P) * P) * Xn := by rw [mul_assoc]
      _ = 0 := by rw [hCompP, zero_mul]
  have hXnYm : Xn * Ym = 0 := by
    calc
      Xn * Ym = (Xn * P) * Ym := by rw [hXnP]
      _ = Xn * (P * Ym) := by rw [mul_assoc]
      _ = 0 := by rw [hPYm, mul_zero]
  have hPYn : P * Yn = 0 := by
    calc
      P * Yn = P * ((1 - P) * Yn) := by
        rw [qgtMinus_defect_iterates_left hP A C n]
      _ = (P * (1 - P)) * Yn := by rw [mul_assoc]
      _ = 0 := by rw [hPComp, zero_mul]
  have hYmXn : Ym * Xn = 0 := by
    calc
      Ym * Xn = (Ym * (1 - P)) * Xn := by rw [hYmComp]
      _ = Ym * ((1 - P) * Xn) := by rw [mul_assoc]
      _ = 0 := by rw [hCompXn, mul_zero]
  have hYnXm : Yn * Xm = 0 := by
    have hCompXm : (1 - P) * Xm = 0 := by
      calc
        (1 - P) * Xm = (1 - P) * (P * Xm) := by rw [hXmLeft]
        _ = ((1 - P) * P) * Xm := by rw [mul_assoc]
        _ = 0 := by rw [hCompP, zero_mul]
    calc
      Yn * Xm = (Yn * (1 - P)) * Xm := by rw [hYnComp]
      _ = Yn * ((1 - P) * Xm) := by rw [mul_assoc]
      _ = 0 := by rw [hCompXm, mul_zero]
  have hYnP : Yn * P = 0 := by
    calc
      Yn * P = (Yn * (1 - P)) * P := by rw [hYnComp]
      _ = Yn * ((1 - P) * P) := by rw [mul_assoc]
      _ = 0 := by rw [hCompP, mul_zero]
  have hYmP : Ym * P = 0 := by
    calc
      Ym * P = (Ym * (1 - P)) * P := by rw [hYmComp]
      _ = Ym * ((1 - P) * P) := by rw [mul_assoc]
      _ = 0 := by rw [hCompP, mul_zero]
  have hXmYn : Xm * Yn = 0 := by
    calc
      Xm * Yn = (Xm * P) * Yn := by rw [hXmP]
      _ = Xm * (P * Yn) := by rw [mul_assoc]
      _ = 0 := by rw [hPYn, mul_zero]
  have hXX : Xn * Xm = Xm * Xn :=
    idempotencyDefect_iterates_commute (qgtPlus P A C) n m
  have hYY : Yn * Ym = Ym * Yn :=
    idempotencyDefect_iterates_commute (qgtMinus P A C) n m
  have hPcurvN : P * (Xn - Yn) = Xn := by
    rw [mul_sub, hXnLeft, hPYn, sub_zero]
  have hCurvNP : (Xn - Yn) * P = Xn := by
    rw [sub_mul, hXnP, hYnP, sub_zero]
  have hPcurvM : P * (Xm - Ym) = Xm := by
    rw [mul_sub, hXmLeft, hPYm, sub_zero]
  have hCurvMP : (Xm - Ym) * P = Xm := by
    rw [sub_mul, hXmP, hYmP, sub_zero]
  have hCurvatureProduct : (Xn - Yn) * (Xm - Ym) =
      Xn * Xm + Yn * Ym := by
    calc
      (Xn - Yn) * (Xm - Ym) = Xn * Xm - Xn * Ym - Yn * Xm + Yn * Ym := by
        noncomm_ring
      _ = Xn * Xm + Yn * Ym := by rw [hXnYm, hYnXm]; noncomm_ring
  have hCurvatureProductRev : (Xm - Ym) * (Xn - Yn) =
      Xm * Xn + Ym * Yn := by
    calc
      (Xm - Ym) * (Xn - Yn) = Xm * Xn - Xm * Yn - Ym * Xn + Ym * Yn := by
        noncomm_ring
      _ = Xm * Xn + Ym * Yn := by rw [hXmYn, hYmXn]; noncomm_ring
  have hStones : (P - (Xn - Yn)) * (P - (Xm - Ym)) =
      (P - (Xm - Ym)) * (P - (Xn - Yn)) := by
    calc
      (P - (Xn - Yn)) * (P - (Xm - Ym)) =
          P * P - P * (Xm - Ym) - (Xn - Yn) * P +
            (Xn - Yn) * (Xm - Ym) := by noncomm_ring
      _ = P - Xm - Xn + Xn * Xm + Yn * Ym := by
        rw [hP, hPcurvM, hCurvNP, hCurvatureProduct]
        noncomm_ring
      _ = P - Xn - Xm + Xm * Xn + Ym * Yn := by
        rw [hXX, hYY]
        abel
      _ = P * P - P * (Xn - Yn) - (Xm - Ym) * P +
            (Xm - Ym) * (Xn - Yn) := by
        rw [hP, hPcurvN, hCurvMP, hCurvatureProductRev]
        noncomm_ring
      _ = (P - (Xm - Ym)) * (P - (Xn - Yn)) := by noncomm_ring
  unfold comm
  change (P - (Xn - Yn)) * (P - (Xm - Ym)) -
      (P - (Xm - Ym)) * (P - (Xn - Yn)) = 0
  rw [hStones, sub_self]

/-- The radical square is `1 + 4` times the next metric level. -/
theorem multiplicatio_radical_square {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    multiplicatioRadical n P A C * multiplicatioRadical n P A C =
      1 + (4 : ℤ) • multiplicatioMetric (n + 1) P A C := by
  unfold multiplicatioRadical
  rw [centered_square_eq_one_add_four_defect,
    multiplicatio_stone_defect hP A C n]

/-- The existing homogenized channels have the checked second-order diagonal
and cross-channel behavior on the tetraktys generators. -/
theorem multiplicatio_mandala_composition_table {P : B}
    (hP : P * P = P) (A C : B) :
    hProjV P A C (hProjV P A C (genV P A C)) =
        (8 : ℤ) • ((genV P A C * genV P A C) *
          hProjV P A C (genV P A C)) ∧
    hProjPhi P A C (hProjPhi P A C (genPhi P A C)) =
        (8 : ℤ) • ((genV P A C * genV P A C) *
          hProjPhi P A C (genPhi P A C)) ∧
    hProjJ P A C (hProjJ P A C (genJ P A C)) =
        (8 : ℤ) • ((genV P A C * genV P A C) *
          hProjJ P A C (genJ P A C)) ∧
    hProjSig P A C (hProjSig P A C (genSig P A C)) =
        (8 : ℤ) • ((genV P A C * genV P A C) *
          hProjSig P A C (genSig P A C)) ∧
    hProjPhi P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjJ P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjSig P A C (hProjV P A C (genV P A C)) = 0 ∧
    hProjV P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjJ P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjSig P A C (hProjPhi P A C (genPhi P A C)) = 0 ∧
    hProjV P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjPhi P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjSig P A C (hProjJ P A C (genJ P A C)) = 0 ∧
    hProjV P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjPhi P A C (hProjSig P A C (genSig P A C)) = 0 ∧
    hProjJ P A C (hProjSig P A C (genSig P A C)) = 0 :=
  archetype_A15_second_order_orthogonality hP A C

/-- Master D₄₇: the full finite-depth stone law, discriminant, Peirce
localization, and the existing checked mandala composition result. -/
theorem stageD47_multiplicatio_logistic_tower {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    multiplicatioMetric (n + 1) P A C =
        idempotencyDefect (multiplicatioMetric n P A C) ∧
    idempotencyDefect (multiplicatioStone n P A C) =
        multiplicatioMetric (n + 1) P A C ∧
    multiplicatioRadical n P A C * multiplicatioRadical n P A C =
        1 + (4 : ℤ) • multiplicatioMetric (n + 1) P A C ∧
    comm P (multiplicatioStone n P A C) = 0 := by
  exact ⟨multiplicatioMetric_succ_eq_defect hP A C n,
    multiplicatio_stone_defect hP A C n,
    multiplicatio_radical_square hP A C n,
    multiplicatio_stone_commutes_with_P hP A C n⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine

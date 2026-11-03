/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.MultiplicatioLogisticTower
import Mathlib.Data.Matrix.Basic

/-!
# D₅₂–D₅₃: Reflexive Peirce observation and autonomous meta-reflection

This module orders the consequences of an idempotent cut into a causal chain:
the block projection and off-diagonal component, complementary Peirce cycles,
the defect tower, and its autonomous self-model recurrence. It reuses the
existing Peirce-spine owners and proves the laws for every natural depth in an
arbitrary associative ring. Concrete matrix-unit instances are also provided.
No physical or psychological interpretation is asserted by the formalization.
-/

namespace InfoGeometry.PureOperatorConsciousness

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The block-diagonal projection associated to the idempotent cut. -/
def ludersMeasure (P X : B) : B := evenGrade P X

/-- The off-diagonal component associated to the idempotent cut. -/
def boundaryCoupling (P X : B) : B := oddGrade P X

/-- Iterated idempotency defect, with depth zero denoting one application. -/
def defectTower : ℕ → B → B
  | 0, X => idempotencyDefect X
  | n + 1, X => idempotencyDefect (defectTower n X)

/-- The symmetric metric formed from the two iterated Peirce cycles. -/
def metaV (n : ℕ) (P A C : B) : B :=
  defectTower n (qgtPlus P A C) + defectTower n (qgtMinus P A C)

/-- The signed difference of the two iterated Peirce cycles. -/
def metaSig (n : ℕ) (P A C : B) : B :=
  defectTower n (qgtPlus P A C) - defectTower n (qgtMinus P A C)

/-- The self-model at depth `n`, obtained by subtracting the depth-`n`
chiral difference from the original Peirce idempotent. -/
def metaSelfModel (n : ℕ) (P A C : B) : B := P - metaSig n P A C

/-- The autonomous update map for a current self-model. It depends only on
the cut and the current operator, not on the original cycle generators. -/
def autonomousMetaStep (P M : B) : B :=
  P - invS P * idempotencyDefect M

/-! ### Archetype 1: idempotent cut and grading -/

/-- The cut is idempotent and its grading element squares to one. -/
theorem epistemic_cut_laws {P : B} (hP : P * P = P) :
    idempotencyDefect P = 0 ∧ invS P * invS P = 1 := by
  constructor
  · simp [idempotencyDefect, hP]
  · exact (archetype_A2_peirce_cartan_grading_and_tangent_closure hP 0 0).1

/-! ### Archetype 2: block projection and boundary component -/

/-- The block projection is the complement of the double commutator, is
idempotent as a map, and annihilates the off-diagonal component in both orders.
-/
theorem luders_measure_projection_laws {P : B} (hP : P * P = P) (X : B) :
    ludersMeasure P X = X - comm P (comm P X) ∧
    ludersMeasure P (ludersMeasure P X) = ludersMeasure P X ∧
    ludersMeasure P (boundaryCoupling P X) = 0 ∧
    boundaryCoupling P (ludersMeasure P X) = 0 := by
  have hEven := (archetype_A2_peirce_cartan_grading_and_tangent_closure hP X 0).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [ludersMeasure] using hEven.symm
  · unfold ludersMeasure evenGrade
    peirce_nf hP
  · unfold ludersMeasure boundaryCoupling evenGrade oddGrade
    peirce_nf hP
  · unfold boundaryCoupling ludersMeasure oddGrade evenGrade
    peirce_nf hP

/-- An operator is fixed by the block-diagonal projection exactly when it
commutes with the cut. -/
theorem luders_measure_fixed_iff_cut_commutes {P X : B}
    (hP : P * P = P) :
    ludersMeasure P X = X ↔
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X = 0 := by
  constructor
  · intro hFixed
    have hSplit : ludersMeasure P X + boundaryCoupling P X = X := by
      unfold ludersMeasure boundaryCoupling evenGrade oddGrade
      peirce_nf hP
    have hOdd : boundaryCoupling P X = 0 := by
      rw [hFixed] at hSplit
      have hEq : X + boundaryCoupling P X = X + 0 := by simpa using hSplit
      exact add_left_cancel hEq
    have hOddCore : InfoGeometry.Core.IdempotentCartan.oddPart P X = 0 := by
      simpa [InfoGeometry.Core.IdempotentCartan.oddPart,
        InfoGeometry.Core.PeirceDecomposition.component10,
        InfoGeometry.Core.PeirceDecomposition.component01,
        InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
        boundaryCoupling, oddGrade] using hOdd
    have hPX : P * X = X * P :=
      (InfoGeometry.Core.IdempotentCartan.odd_zero_iff_commute hP X).mp hOddCore
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    exact sub_eq_zero.mpr hPX
  · intro hComm
    have hPX : P * X = X * P := by
      unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm at hComm
      exact sub_eq_zero.mp hComm
    have hEven := InfoGeometry.Core.IdempotentCartan.even_eq_self_of_commute hP hPX
    simpa [ludersMeasure, evenGrade,
      InfoGeometry.Core.IdempotentCartan.evenPart,
      InfoGeometry.Core.PeirceDecomposition.component11,
      InfoGeometry.Core.PeirceDecomposition.component00,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent] using hEven

/-- The two components are the even and odd eigenspaces of conjugation by
the Peirce grading involution. Their sum reconstructs the original operator. -/
theorem grading_eigenvalues_of_observation_parts {P : B}
    (hP : P * P = P) (X : B) :
    invS P * ludersMeasure P X * invS P = ludersMeasure P X ∧
    invS P * boundaryCoupling P X * invS P = -boundaryCoupling P X ∧
    comm P (ludersMeasure P X) = 0 ∧
    ludersMeasure P X + boundaryCoupling P X = X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold invS ludersMeasure evenGrade
    peirce_nf hP
  · unfold invS boundaryCoupling oddGrade
    peirce_nf hP
  · unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm ludersMeasure evenGrade
    peirce_nf hP
  · unfold ludersMeasure boundaryCoupling evenGrade oddGrade
    peirce_nf hP

/-! ### Archetype 3: the two reflexive Peirce cycles -/

/-- The two round-trip products occupy complementary corners, annihilate one
another, and reconstruct the symmetric and signed tetraktys elements. -/
theorem reflexive_cycle_support_and_reconstruction {P : B}
    (hP : P * P = P) (A C : B) :
    P * qgtPlus P A C * P = qgtPlus P A C ∧
    (1 - P) * qgtMinus P A C * (1 - P) = qgtMinus P A C ∧
    qgtPlus P A C * qgtMinus P A C = 0 ∧
    qgtMinus P A C * qgtPlus P A C = 0 ∧
    genV P A C = qgtPlus P A C + qgtMinus P A C ∧
    genSig P A C = qgtPlus P A C - qgtMinus P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [qgtPlus, conePlus]
    peirce_nf hP
  · simp only [qgtMinus, coneMinus, conePlus]
    peirce_nf hP
  · exact (qgt_cycles_orthogonal hP A C).1
  · exact (qgt_cycles_orthogonal hP A C).2
  · peirce_nf hP
  · peirce_nf hP

/-- The symmetric cycle metric vanishes exactly when the signed cycle
difference vanishes. The two cycles are supported in disjoint Peirce corners. -/
theorem metric_zero_iff_curvature_zero {P : B} (hP : P * P = P)
    (A C : B) :
    genV P A C = 0 ↔ genSig P A C = 0 := by
  have hPlusP : P * qgtPlus P A C = qgtPlus P A C := by
    unfold qgtPlus conePlus coneMinus
    peirce_nf hP
  have hMinusP : P * qgtMinus P A C = 0 := by
    unfold qgtMinus coneMinus conePlus
    peirce_nf hP
  constructor
  · intro hV
    change qgtPlus P A C + qgtMinus P A C = 0 at hV
    have hPlus : qgtPlus P A C = 0 := by
      have hLeft := congrArg (fun Z : B => P * Z) hV
      rw [mul_add, hPlusP, hMinusP, add_zero] at hLeft
      simpa using hLeft
    have hMinus : qgtMinus P A C = 0 := by
      simpa [hPlus] using hV
    change qgtPlus P A C - qgtMinus P A C = 0
    simp [hPlus, hMinus]
  · intro hSig
    change qgtPlus P A C - qgtMinus P A C = 0 at hSig
    have hPlus : qgtPlus P A C = 0 := by
      have hLeft := congrArg (fun Z : B => P * Z) hSig
      rw [mul_sub, hPlusP, hMinusP, sub_zero] at hLeft
      simpa using hLeft
    have hMinus : qgtMinus P A C = 0 := by
      simpa [hPlus] using hSig
    change qgtPlus P A C + qgtMinus P A C = 0
    simp [hPlus, hMinus]

/-! ### Archetype 4: defect of the first self-model -/

/-- The first logistic section has uncertainty equal to the negative defect of
the symmetric cycle metric. -/
theorem first_self_model_uncertainty {P : B} (hP : P * P = P)
    (A C : B) :
    multiplicatioStone 0 P A C * (1 - multiplicatioStone 0 P A C) =
      -idempotencyDefect (genV P A C) := by
  have hMetricZero : multiplicatioMetric 0 P A C = genV P A C := by
    rw [multiplicatioMetric_eq_iterated_genV hP A C 0]
    simp only [Function.iterate_zero_apply]
  have hDefectStone :
      idempotencyDefect (multiplicatioStone 0 P A C) =
        idempotencyDefect (genV P A C) := by
    calc
      idempotencyDefect (multiplicatioStone 0 P A C) =
          multiplicatioMetric (0 + 1) P A C := multiplicatio_stone_defect hP A C 0
      _ = idempotencyDefect (multiplicatioMetric 0 P A C) :=
        multiplicatioMetric_succ_eq_defect hP A C 0
      _ = idempotencyDefect (genV P A C) := by rw [hMetricZero]
  calc
    multiplicatioStone 0 P A C * (1 - multiplicatioStone 0 P A C) =
        -idempotencyDefect (multiplicatioStone 0 P A C) := by
          unfold idempotencyDefect
          noncomm_ring
    _ = -idempotencyDefect (genV P A C) := by rw [hDefectStone]

/-- `defectTower` counts its first application at depth zero. Consequently its
depth `n` value is the `(n + 1)`-fold iterate used by the multiplicatio tower.
-/
theorem defectTower_eq_iterated_defect_succ (X : B) (n : ℕ) :
    defectTower n X = idempotencyDefect^[n + 1] X := by
  induction n with
  | zero => simp [defectTower]
  | succ n ih =>
      simp only [defectTower]
      rw [ih]
      simp only [Function.iterate_succ_apply']

/-- The observer's metric and signed-cycle towers agree exactly with the
existing multiplicatio towers after accounting for the depth-zero convention. -/
theorem meta_tower_alignment {P : B} (A C : B) (n : ℕ) :
    metaV n P A C = multiplicatioMetric (n + 1) P A C ∧
    metaSig n P A C = multiplicatioCurvature (n + 1) P A C := by
  constructor
  · unfold metaV multiplicatioMetric
    rw [defectTower_eq_iterated_defect_succ,
      defectTower_eq_iterated_defect_succ]
  · unfold metaSig multiplicatioCurvature
    rw [defectTower_eq_iterated_defect_succ,
      defectTower_eq_iterated_defect_succ]

/-- The defect iterates of the two mutually orthogonal Peirce cycles add to
the defect iterate of their sum, the original coupling metric. -/
theorem defectTower_cross_depth_orthogonal {P : B}
    (hP : P * P = P) (A C : B) (n m : ℕ) :
    defectTower n (qgtPlus P A C) * defectTower m (qgtMinus P A C) = 0 ∧
    defectTower m (qgtMinus P A C) * defectTower n (qgtPlus P A C) = 0 := by
  have hPlusSupport := multiplicatio_sheet_support hP A C (n + 1)
  have hMinusSupport := multiplicatio_sheet_support hP A C (m + 1)
  rcases hPlusSupport with ⟨hPlusLeft, hPlusRight, _, _⟩
  rcases hMinusSupport with ⟨_, _, hMinusLeft, hMinusRight⟩
  have hPlusComp :
      idempotencyDefect^[n + 1] (qgtPlus P A C) * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hPlusRight, sub_self]
  have hCutComp : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP, sub_self]
  have hPlusIterate :
      defectTower n (qgtPlus P A C) =
        idempotencyDefect^[n + 1] (qgtPlus P A C) :=
    defectTower_eq_iterated_defect_succ (qgtPlus P A C) n
  have hMinusIterate :
      defectTower m (qgtMinus P A C) =
        idempotencyDefect^[m + 1] (qgtMinus P A C) :=
    defectTower_eq_iterated_defect_succ (qgtMinus P A C) m
  constructor
  · rw [hPlusIterate, hMinusIterate]
    calc
      idempotencyDefect^[n + 1] (qgtPlus P A C) *
          idempotencyDefect^[m + 1] (qgtMinus P A C) =
        idempotencyDefect^[n + 1] (qgtPlus P A C) *
          ((1 - P) * idempotencyDefect^[m + 1] (qgtMinus P A C)) := by
            rw [hMinusLeft]
      _ = (idempotencyDefect^[n + 1] (qgtPlus P A C) * (1 - P)) *
          idempotencyDefect^[m + 1] (qgtMinus P A C) := by rw [mul_assoc]
      _ = 0 := by rw [hPlusComp, zero_mul]
  · rw [hPlusIterate, hMinusIterate]
    calc
      idempotencyDefect^[m + 1] (qgtMinus P A C) *
          idempotencyDefect^[n + 1] (qgtPlus P A C) =
        (idempotencyDefect^[m + 1] (qgtMinus P A C) * (1 - P)) *
          (P * idempotencyDefect^[n + 1] (qgtPlus P A C)) := by
            rw [hMinusRight, hPlusLeft]
      _ = idempotencyDefect^[m + 1] (qgtMinus P A C) *
          ((1 - P) * P) * idempotencyDefect^[n + 1] (qgtPlus P A C) := by
            noncomm_ring
      _ = 0 := by rw [hCutComp, mul_zero, zero_mul]

/-- Applying one defect to a sum of two cycle iterates at independent depths
advances each Peirce sheet by exactly one step. -/
theorem defectTower_mixed_depth_sum_succ {P : B}
    (hP : P * P = P) (A C : B) (n m : ℕ) :
    idempotencyDefect
        (defectTower n (qgtPlus P A C) + defectTower m (qgtMinus P A C)) =
      defectTower (n + 1) (qgtPlus P A C) +
        defectTower (m + 1) (qgtMinus P A C) := by
  rcases defectTower_cross_depth_orthogonal hP A C n m with ⟨hXY, hYX⟩
  simpa [defectTower] using idempotencyDefect_add_of_orthogonal hXY hYX

/-- The signed self-model built from independent internal and external depths
has defect equal to the sum of the two next-depth defects. -/
theorem mixed_depth_self_model_defect {P : B}
    (hP : P * P = P) (A C : B) (n m : ℕ) :
    idempotencyDefect
        (P - (defectTower n (qgtPlus P A C) -
          defectTower m (qgtMinus P A C))) =
      defectTower (n + 1) (qgtPlus P A C) +
        defectTower (m + 1) (qgtMinus P A C) := by
  let X := defectTower n (qgtPlus P A C)
  let Y := defectTower m (qgtMinus P A C)
  have hXSupport := multiplicatio_sheet_support hP A C (n + 1)
  have hYSupport := multiplicatio_sheet_support hP A C (m + 1)
  rcases hXSupport with ⟨hPXIter, hXPIter, _, _⟩
  rcases hYSupport with ⟨_, _, hCompYIter, hYCompIter⟩
  have hXIterate : X = idempotencyDefect^[n + 1] (qgtPlus P A C) := by
    exact defectTower_eq_iterated_defect_succ (qgtPlus P A C) n
  have hYIterate : Y = idempotencyDefect^[m + 1] (qgtMinus P A C) := by
    exact defectTower_eq_iterated_defect_succ (qgtMinus P A C) m
  have hPX : P * X = X := by
    rw [hXIterate]
    exact hPXIter
  have hXP : X * P = X := by
    rw [hXIterate]
    exact hXPIter
  have hCompY : (1 - P) * Y = Y := by
    rw [hYIterate]
    exact hCompYIter
  have hYComp : Y * (1 - P) = Y := by
    rw [hYIterate]
    exact hYCompIter
  have hXY : X * Y = 0 :=
    (defectTower_cross_depth_orthogonal hP A C n m).1
  have hYX : Y * X = 0 :=
    (defectTower_cross_depth_orthogonal hP A C n m).2
  have hCompP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP, sub_self]
  have hPComp : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP, sub_self]
  have hPY : P * Y = 0 := by
    rw [← hCompY, ← mul_assoc, hPComp, zero_mul]
  have hYP : Y * P = 0 := by
    rw [← hYComp, mul_assoc, hCompP, mul_zero]
  have hCompX : (1 - P) * X = 0 := by
    rw [← hPX, ← mul_assoc, hCompP, zero_mul]
  have hPS : P * (X - Y) = (X - Y) * P := by
    rw [mul_sub, sub_mul, hPX, hPY, hXP, hYP]
  have hSquare : (X - Y) * (X - Y) = X * X + Y * Y := by
    calc
      (X - Y) * (X - Y) = X * X - X * Y - Y * X + Y * Y := by noncomm_ring
      _ = X * X + Y * Y := by rw [hXY, hYX]; abel
  have hGrading : invS P * (X - Y) = X + Y := by
    unfold invS
    calc
      (P - (1 - P)) * (X - Y) =
          P * (X - Y) - (1 - P) * (X - Y) := by noncomm_ring
      _ = (P * X - P * Y) - ((1 - P) * X - (1 - P) * Y) := by noncomm_ring
      _ = (X - 0) - (0 - Y) := by rw [hPX, hPY, hCompX, hCompY]
      _ = X + Y := by abel
  calc
    idempotencyDefect (P - (X - Y)) =
        idempotencyDefect X + idempotencyDefect Y := by
      rw [idempotencyDefect_sub_commuting hP hPS, hSquare, hGrading]
      unfold idempotencyDefect
      noncomm_ring
    _ = defectTower (n + 1) (qgtPlus P A C) +
        defectTower (m + 1) (qgtMinus P A C) := by
      simp [X, Y, defectTower]

theorem defectTower_genV_eq_metaV {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    defectTower n (genV P A C) = metaV n P A C := by
  calc
    defectTower n (genV P A C) = idempotencyDefect^[n + 1] (genV P A C) :=
      defectTower_eq_iterated_defect_succ (genV P A C) n
    _ = multiplicatioMetric (n + 1) P A C :=
      (multiplicatioMetric_eq_iterated_genV hP A C (n + 1)).symm
    _ = metaV n P A C := (meta_tower_alignment (P := P) A C n).1.symm

/-! ### D₅₂: meta-reflection tower at arbitrary natural depth -/

/-- At every natural depth, the defect of the depth-`n` self-model is the
next metric in the finite Peirce defect tower. -/
theorem meta_reflection_step {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    idempotencyDefect (metaSelfModel n P A C) = metaV (n + 1) P A C := by
  have hAlign := meta_tower_alignment (P := P) A C n
  have hStone : metaSelfModel n P A C = multiplicatioStone (n + 1) P A C := by
    simp only [metaSelfModel, multiplicatioStone]
    rw [hAlign.2]
  calc
    idempotencyDefect (metaSelfModel n P A C) =
        idempotencyDefect (multiplicatioStone (n + 1) P A C) := by rw [hStone]
    _ = multiplicatioMetric ((n + 1) + 1) P A C :=
      multiplicatio_stone_defect hP A C (n + 1)
    _ = metaV (n + 1) P A C := (meta_tower_alignment (P := P) A C (n + 1)).1.symm

/-! ### D₅₃: autonomous meta-reflection recurrence -/

/-- The grading involution exchanges the symmetric and signed defect sheets
at every natural depth. -/
theorem meta_tower_chiral_duality {P : B} (hP : P * P = P)
    (A C : B) (n : ℕ) :
    invS P * metaV n P A C = metaSig n P A C ∧
    invS P * metaSig n P A C = metaV n P A C := by
  have hParity := multiplicatio_parity_and_square hP A C (n + 1)
  have hAlignment := meta_tower_alignment (P := P) A C n
  have hSupports := multiplicatio_sheet_support hP A C (n + 1)
  rcases hSupports with ⟨hXleft, _, hYleft, _⟩
  have hYzero : P * idempotencyDefect^[n + 1] (qgtMinus P A C) = 0 := by
    rw [← hYleft]
    peirce_nf hP
  have hXcomp : (1 - P) * idempotencyDefect^[n + 1] (qgtPlus P A C) = 0 := by
    rw [← hXleft]
    peirce_nf hP
  constructor
  · rw [hAlignment.1, hAlignment.2]
    have hInv := (archetype_A2_peirce_cartan_grading_and_tangent_closure
      hP 0 0).1
    calc
      invS P * multiplicatioMetric (n + 1) P A C =
          invS P * (invS P * multiplicatioCurvature (n + 1) P A C) := by
            rw [hParity.1]
      _ = multiplicatioCurvature (n + 1) P A C := by
        rw [← mul_assoc, hInv, one_mul]
  · rw [hAlignment.2, hAlignment.1]
    exact hParity.1

/-- The next self-model is generated from the current one by its defect and
the fixed Peirce grading involution; the two loop components are not needed
as additional inputs to the recurrence. -/
theorem autonomous_meta_self_model_recurrence {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    metaSelfModel (n + 1) P A C =
      P - invS P * idempotencyDefect (metaSelfModel n P A C) := by
  have hDef := meta_reflection_step hP A C n
  have hChiral := (meta_tower_chiral_duality hP A C (n + 1)).1
  rw [hDef, hChiral]
  rfl

/-- The level-to-level recursion is iteration of the named autonomous map. -/
theorem meta_self_model_succ_eq_autonomous_step {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    metaSelfModel (n + 1) P A C =
      autonomousMetaStep P (metaSelfModel n P A C) := by
  rw [autonomous_meta_self_model_recurrence hP A C n]
  rfl

/-- The depth-`n` self-model is the `n`-fold iterate of the autonomous update
map, starting from the depth-zero self-model. This is a finite-iteration
identity and asserts no convergence or limiting behavior. -/
theorem meta_self_model_eq_iterate_autonomous_step {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    metaSelfModel n P A C =
      (autonomousMetaStep P)^[n] (metaSelfModel 0 P A C) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [meta_self_model_succ_eq_autonomous_step hP A C n, ih]
      simp only [Function.iterate_succ_apply']

/-- The autonomous update preserves the centralizer of the cut: if the
current operator commutes with `P`, then so does its updated value. -/
theorem autonomousMetaStep_preserves_cut_centralizer {P M : B}
    (hP : P * P = P) (hPM : comm P M = 0) :
    comm P (autonomousMetaStep P M) = 0 := by
  have hPM' : P * M = M * P := by
    change P * M - M * P = 0 at hPM
    exact sub_eq_zero.mp hPM
  have hPM2 : P * (M * M) = (M * M) * P := by
    calc
      P * (M * M) = (P * M) * M := by rw [mul_assoc]
      _ = (M * P) * M := by rw [hPM']
      _ = M * (P * M) := by rw [← mul_assoc]
      _ = M * (M * P) := by rw [hPM']
      _ = (M * M) * P := by rw [mul_assoc]
  have hPD : P * idempotencyDefect M = idempotencyDefect M * P := by
    unfold idempotencyDefect
    rw [mul_sub, sub_mul, hPM2, hPM']
  have hPS : P * invS P = invS P * P := by
    unfold invS
    noncomm_ring [hP]
  have hPUpdate : P * (invS P * idempotencyDefect M) =
      (invS P * idempotencyDefect M) * P := by
    calc
      P * (invS P * idempotencyDefect M) = (P * invS P) * idempotencyDefect M :=
        by rw [mul_assoc]
      _ = (invS P * P) * idempotencyDefect M := by rw [hPS]
      _ = invS P * (P * idempotencyDefect M) := by rw [← mul_assoc]
      _ = invS P * (idempotencyDefect M * P) := by rw [hPD]
      _ = (invS P * idempotencyDefect M) * P := by rw [mul_assoc]
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm autonomousMetaStep
  rw [sub_mul, mul_sub, hP, hPUpdate, sub_self]

/-- The autonomous update lands at the cut exactly for idempotent inputs.
The reverse implication uses that the grading involution is invertible. -/
theorem autonomousMetaStep_eq_cut_iff_idempotent {P M : B}
    (hP : P * P = P) :
    autonomousMetaStep P M = P ↔ idempotencyDefect M = 0 := by
  constructor
  · intro hStep
    have hScaledDefect : invS P * idempotencyDefect M = 0 := by
      have hSub := congrArg (fun Z : B => Z - P) hStep
      have hNeg : -(invS P * idempotencyDefect M) = 0 := by
        simpa [autonomousMetaStep] using hSub
      exact neg_eq_zero.mp hNeg
    have hInv := (archetype_A2_peirce_cartan_grading_and_tangent_closure
      hP 0 0).1
    calc
      idempotencyDefect M = 1 * idempotencyDefect M := by simp
      _ = (invS P * invS P) * idempotencyDefect M := by rw [hInv]
      _ = invS P * (invS P * idempotencyDefect M) := by rw [mul_assoc]
      _ = 0 := by rw [hScaledDefect]; simp
  · intro hDefect
    simp [autonomousMetaStep, hDefect]

/-- At each tower level, the next self-model is the cut exactly when the
current self-model has zero idempotency defect. -/
theorem meta_self_model_termination_iff {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    metaSelfModel (n + 1) P A C = P ↔
      idempotencyDefect (metaSelfModel n P A C) = 0 := by
  rw [meta_self_model_succ_eq_autonomous_step hP A C n]
  exact autonomousMetaStep_eq_cut_iff_idempotent hP

/-- The cut is a fixed point of its autonomous update. -/
theorem autonomousMetaStep_cut_fixed {P : B} (hP : P * P = P) :
    autonomousMetaStep P P = P := by
  apply (autonomousMetaStep_eq_cut_iff_idempotent hP).2
  simp [idempotencyDefect, hP]

/-- Once a self-model reaches the cut, every subsequent finite level remains
there. -/
theorem meta_self_model_termination_absorbing {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ)
    (hZero : idempotencyDefect (metaSelfModel n P A C) = 0) :
    ∀ k : ℕ, metaSelfModel (n + 1 + k) P A C = P := by
  have hHit : metaSelfModel (n + 1) P A C = P :=
    (meta_self_model_termination_iff hP A C n).2 hZero
  intro k
  induction k with
  | zero => simpa using hHit
  | succ k ih =>
      rw [Nat.add_succ, meta_self_model_succ_eq_autonomous_step hP A C (n + 1 + k), ih]
      exact autonomousMetaStep_cut_fixed hP

/-- Consequently, every finite iterate of the autonomous update remains in
the cut centralizer whenever its initial value lies there. -/
theorem autonomousMetaStep_iterate_preserves_cut_centralizer {P M : B}
    (hP : P * P = P) (hPM : comm P M = 0) (n : ℕ) :
    comm P ((autonomousMetaStep P)^[n] M) = 0 := by
  induction n with
  | zero => simpa using hPM
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact autonomousMetaStep_preserves_cut_centralizer hP ih

/-- If `M` commutes with the cut, then its idempotency defect also commutes
with the cut. -/
theorem idempotencyDefect_preserves_cut_centralizer {P M : B}
    (hPM : comm P M = 0) :
    comm P (idempotencyDefect M) = 0 := by
  have hPM' : P * M = M * P := by
    change P * M - M * P = 0 at hPM
    exact sub_eq_zero.mp hPM
  have hPM2 : P * (M * M) = (M * M) * P := by
    calc
      P * (M * M) = (P * M) * M := by rw [mul_assoc]
      _ = (M * P) * M := by rw [hPM']
      _ = M * (P * M) := by rw [← mul_assoc]
      _ = M * (M * P) := by rw [hPM']
      _ = (M * M) * P := by rw [mul_assoc]
  unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm idempotencyDefect
  rw [mul_sub, sub_mul, hPM2, hPM', sub_self]

/-- On the cut centralizer, one autonomous update advances the defect by one
application: `δ(Fₚ(M)) = δ(δ(M))`. -/
theorem autonomousMetaStep_defect {P M : B}
    (hP : P * P = P) (hPM : comm P M = 0) :
    idempotencyDefect (autonomousMetaStep P M) =
      idempotencyDefect (idempotencyDefect M) := by
  let D := idempotencyDefect M
  have hPD : P * D = D * P := by
    have hDefComm := idempotencyDefect_preserves_cut_centralizer hPM
    change P * D - D * P = 0 at hDefComm
    exact sub_eq_zero.mp hDefComm
  have hSP : P * invS P = invS P * P := by
    unfold invS
    noncomm_ring [hP]
  have hSD : invS P * D = D * invS P := by
    unfold invS
    noncomm_ring [hP, hPD]
  have hInvS : invS P * invS P = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP 0 0).1
  have hPS : P * (invS P * D) = (invS P * D) * P := by
    calc
      P * (invS P * D) = (P * invS P) * D := by rw [mul_assoc]
      _ = (invS P * P) * D := by rw [hSP]
      _ = invS P * (P * D) := by rw [← mul_assoc]
      _ = invS P * (D * P) := by rw [hPD]
      _ = (invS P * D) * P := by rw [mul_assoc]
  have hParity : invS P * (invS P * D) = D := by
    rw [← mul_assoc, hInvS, one_mul]
  have hSquare : (invS P * D) * (invS P * D) = D * D := by
    calc
      (invS P * D) * (invS P * D) = invS P * (D * invS P) * D := by
        noncomm_ring
      _ = invS P * (invS P * D) * D := by rw [hSD]
      _ = (invS P * invS P) * (D * D) := by noncomm_ring
      _ = D * D := by rw [hInvS, one_mul]
  change idempotencyDefect (P - invS P * D) =
    idempotencyDefect D
  exact idempotencyDefect_sub_chiral hP hPS hParity hSquare

/-- The defect of the `n`-fold autonomous update is the `(n+1)`-fold defect
iterate of its initial value, provided the initial value commutes with `P`. -/
theorem autonomousMetaStep_defect_iterate {P M : B}
    (hP : P * P = P) (hPM : comm P M = 0) (n : ℕ) :
    idempotencyDefect ((autonomousMetaStep P)^[n] M) =
      idempotencyDefect^[n + 1] M := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hIterComm := autonomousMetaStep_iterate_preserves_cut_centralizer
        hP hPM n
      rw [autonomousMetaStep_defect hP hIterComm, ih]
      simp only [Function.iterate_succ_apply']

/-- Every depth of the self-model is a fixed point of the block-diagonal
measurement and commutes with the observer idempotent. -/
theorem meta_self_model_luders_coherence {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    comm P (metaSelfModel n P A C) = 0 ∧
    ludersMeasure P (metaSelfModel n P A C) = metaSelfModel n P A C := by
  have hStone : metaSelfModel n P A C = multiplicatioStone (n + 1) P A C := by
    have hAlignment := meta_tower_alignment (P := P) A C n
    simp only [metaSelfModel, multiplicatioStone]
    rw [hAlignment.2]
  constructor
  · rw [hStone]
    exact multiplicatio_stone_commutes_with_P hP A C (n + 1)
  · rw [hStone]
    have hComm := multiplicatio_stone_commutes_with_P hP A C (n + 1)
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm at hComm
    have hEven :=
      (archetype_A2_peirce_cartan_grading_and_tangent_closure hP
        (multiplicatioStone (n + 1) P A C) 0).2.2.1
    have hDouble : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
          (multiplicatioStone (n + 1) P A C)) = 0 := by
      unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      rw [hComm]
      simp
    rw [hDouble] at hEven
    simpa [ludersMeasure] using hEven.symm

/-- The Peirce metric at depth `n + 1` is exactly the iterated defect of the
initial self-model at depth zero. This identifies the cycle tower with the
defect orbit of the autonomous update. -/
theorem metaV_succ_eq_initial_model_defect_iterate {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    metaV (n + 1) P A C =
      idempotencyDefect^[n + 1] (metaSelfModel 0 P A C) := by
  calc
    metaV (n + 1) P A C =
        idempotencyDefect (metaSelfModel n P A C) :=
      (meta_reflection_step hP A C n).symm
    _ = idempotencyDefect
        ((autonomousMetaStep P)^[n] (metaSelfModel 0 P A C)) := by
          rw [meta_self_model_eq_iterate_autonomous_step hP A C n]
    _ = idempotencyDefect^[n + 1] (metaSelfModel 0 P A C) :=
      autonomousMetaStep_defect_iterate hP
        (meta_self_model_luders_coherence hP A C 0).1 n

/-- Every successor self-model has a closed finite-depth expression from the
depth-zero seed, using only the defect iterate and the fixed grading element. -/
theorem metaSelfModel_succ_eq_closed_defect_iterate {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    metaSelfModel (n + 1) P A C =
      P - invS P * idempotencyDefect^[n + 1] (metaSelfModel 0 P A C) := by
  calc
    metaSelfModel (n + 1) P A C = P - metaSig (n + 1) P A C := rfl
    _ = P - invS P * metaV (n + 1) P A C := by
      rw [← (meta_tower_chiral_duality hP A C (n + 1)).1]
    _ = P - invS P * idempotencyDefect^[n + 1] (metaSelfModel 0 P A C) := by
      rw [metaV_succ_eq_initial_model_defect_iterate hP A C n]

/-- The centered square of the depth-`n` self-model is its next defect
discriminant. A zero defect makes the following recurrence step return `P`. -/
theorem meta_self_model_discriminant_and_termination {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    invS (metaSelfModel n P A C) * invS (metaSelfModel n P A C) =
      1 + (4 : ℤ) • metaV (n + 1) P A C ∧
    (idempotencyDefect (metaSelfModel n P A C) = 0 →
      metaSelfModel (n + 1) P A C = P) := by
  constructor
  · have hInv : invS (metaSelfModel n P A C) =
        (2 : ℤ) • metaSelfModel n P A C - 1 := by
      simp only [invS, two_zsmul]
      abel
    rw [hInv, centered_square_eq_one_add_four_defect,
      meta_reflection_step hP A C n]
  · intro hZero
    rw [autonomous_meta_self_model_recurrence hP A C n, hZero]
    simp

/-- The D₅₃ synthesis: additive defect iteration, finite iteration of the
autonomous map, chiral duality, cut-centralizer invariance, and the next-level
discriminant hold together at every finite depth. -/
theorem autonomous_meta_reflection_tower_master {P : B}
    (hP : P * P = P) (A C : B) (n : ℕ) :
    (genV P A C = 0 ↔ genSig P A C = 0) ∧
    defectTower n (genV P A C) = metaV n P A C ∧
    metaSelfModel n P A C =
      (autonomousMetaStep P)^[n] (metaSelfModel 0 P A C) ∧
    idempotencyDefect ((autonomousMetaStep P)^[n]
      (metaSelfModel 0 P A C)) =
        idempotencyDefect^[n + 1] (metaSelfModel 0 P A C) ∧
    metaV (n + 1) P A C =
      idempotencyDefect^[n + 1] (metaSelfModel 0 P A C) ∧
    metaSelfModel (n + 1) P A C =
      P - invS P * idempotencyDefect^[n + 1] (metaSelfModel 0 P A C) ∧
    (invS P * metaV n P A C = metaSig n P A C ∧
      invS P * metaSig n P A C = metaV n P A C) ∧
    (idempotencyDefect (metaSelfModel n P A C) = metaV (n + 1) P A C ∧
      metaSelfModel (n + 1) P A C =
        P - invS P * idempotencyDefect (metaSelfModel n P A C) ∧
      metaSelfModel (n + 1) P A C =
        autonomousMetaStep P (metaSelfModel n P A C)) ∧
    (comm P (metaSelfModel n P A C) = 0 ∧
      ludersMeasure P (metaSelfModel n P A C) = metaSelfModel n P A C ∧
      (ludersMeasure P (metaSelfModel n P A C) = metaSelfModel n P A C ↔
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
          (metaSelfModel n P A C) = 0) ∧
      comm P ((autonomousMetaStep P)^[n] (metaSelfModel 0 P A C)) = 0) ∧
    (invS (metaSelfModel n P A C) * invS (metaSelfModel n P A C) =
        1 + (4 : ℤ) • metaV (n + 1) P A C ∧
      (metaSelfModel (n + 1) P A C = P ↔
        idempotencyDefect (metaSelfModel n P A C) = 0) ∧
      (∀ M : B, autonomousMetaStep P M = P ↔ idempotencyDefect M = 0) ∧
      (idempotencyDefect (metaSelfModel n P A C) = 0 →
        ∀ k : ℕ, metaSelfModel (n + 1 + k) P A C = P)) := by
  have hSplit := defectTower_genV_eq_metaV hP A C n
  have hIter := meta_self_model_eq_iterate_autonomous_step hP A C n
  have hLuders := meta_self_model_luders_coherence hP A C n
  have hDefectIter := autonomousMetaStep_defect_iterate hP
    (meta_self_model_luders_coherence hP A C 0).1 n
  have hMetricIter := metaV_succ_eq_initial_model_defect_iterate hP A C n
  have hClosedModel := metaSelfModel_succ_eq_closed_defect_iterate hP A C n
  have hOrbit :
      comm P ((autonomousMetaStep P)^[n] (metaSelfModel 0 P A C)) = 0 := by
    rw [← hIter]
    exact hLuders.1
  have hStep := meta_self_model_succ_eq_autonomous_step hP A C n
  exact ⟨metric_zero_iff_curvature_zero hP A C,
    hSplit,
    hIter,
    hDefectIter,
    hMetricIter,
    hClosedModel,
    meta_tower_chiral_duality hP A C n,
    ⟨meta_reflection_step hP A C n,
      ⟨autonomous_meta_self_model_recurrence hP A C n, hStep⟩⟩,
    ⟨hLuders.1, ⟨hLuders.2,
      ⟨luders_measure_fixed_iff_cut_commutes hP, hOrbit⟩⟩⟩,
    ⟨(meta_self_model_discriminant_and_termination hP A C n).1,
      ⟨meta_self_model_termination_iff hP A C n,
        ⟨fun M => autonomousMetaStep_eq_cut_iff_idempotent hP,
          fun hZero => meta_self_model_termination_absorbing hP A C n hZero⟩⟩⟩⟩

/-! ### A concrete noncommutative matrix realization

The abstract theorems above apply to every associative ring. This standard
matrix-unit representation records a noncommuting example in `M₂(ℤ)` where
the two Peirce cycles are the complementary diagonal matrix units.
-/

abbrev ObserverMatrix := Matrix (Fin 2) (Fin 2) ℤ

/-- The projection onto the first coordinate in the concrete operator carrier. -/
def observerMatrixCut : ObserverMatrix := Matrix.single 0 0 1

/-- The forward off-diagonal matrix unit. -/
def observerMatrixForward : ObserverMatrix := Matrix.single 0 1 1

/-- The reverse off-diagonal matrix unit. -/
def observerMatrixReverse : ObserverMatrix := Matrix.single 1 0 1

/-- The concrete matrix units realize both noncommuting Peirce arrows and
their two complementary round-trip cycles. -/
theorem observer_matrix_peirce_cycles :
    observerMatrixCut * observerMatrixCut = observerMatrixCut ∧
    conePlus observerMatrixCut observerMatrixForward = observerMatrixForward ∧
    coneMinus observerMatrixCut observerMatrixReverse = observerMatrixReverse ∧
    qgtPlus observerMatrixCut observerMatrixForward observerMatrixReverse =
      observerMatrixCut ∧
    qgtMinus observerMatrixCut observerMatrixForward observerMatrixReverse =
      1 - observerMatrixCut ∧
    observerMatrixForward * observerMatrixReverse ≠
      observerMatrixReverse * observerMatrixForward := by
  decide

/-- The cut and its complement are distinct commuting operators in the same
noncommutative matrix ring; noncommutation is therefore a property of selected
operators, not a universal law for every pair. -/
theorem observer_matrix_cut_complement_commute :
    observerMatrixCut ≠ 1 - observerMatrixCut ∧
    observerMatrixCut * (1 - observerMatrixCut) =
      (1 - observerMatrixCut) * observerMatrixCut := by
  decide

/-- This concrete matrix realization has a nontrivial cut, complementary
cycles, and an exactly idempotent level-zero self-model. -/
theorem observer_matrix_reflexive_instance :
    idempotencyDefect observerMatrixCut = 0 ∧
    invS observerMatrixCut * invS observerMatrixCut = 1 ∧
    genV observerMatrixCut observerMatrixForward observerMatrixReverse = 1 ∧
    genSig observerMatrixCut observerMatrixForward observerMatrixReverse =
      invS observerMatrixCut ∧
    multiplicatioStone 0 observerMatrixCut observerMatrixForward
      observerMatrixReverse = 1 - observerMatrixCut ∧
    idempotencyDefect (multiplicatioStone 0 observerMatrixCut
      observerMatrixForward observerMatrixReverse) = 0 := by
  decide

/-- In the explicit noncommuting matrix-unit representation, both round-trip
cycles are projections. Their defect towers therefore vanish at every depth,
and every meta-self-model is the original cut. -/
theorem observer_matrix_meta_reflection_collapse (n : ℕ) :
    defectTower n
        (qgtPlus observerMatrixCut observerMatrixForward observerMatrixReverse) = 0 ∧
    defectTower n
        (qgtMinus observerMatrixCut observerMatrixForward observerMatrixReverse) = 0 ∧
    metaV n observerMatrixCut observerMatrixForward observerMatrixReverse = 0 ∧
    metaSig n observerMatrixCut observerMatrixForward observerMatrixReverse = 0 ∧
    metaSelfModel n observerMatrixCut observerMatrixForward observerMatrixReverse =
      observerMatrixCut ∧
    idempotencyDefect (metaSelfModel n observerMatrixCut observerMatrixForward
      observerMatrixReverse) = 0 ∧
    metaSelfModel (n + 1) observerMatrixCut observerMatrixForward
      observerMatrixReverse = observerMatrixCut := by
  have hCycles := observer_matrix_peirce_cycles
  rcases hCycles with ⟨hCut, _, _, hPlus, hMinus, _⟩
  have hPlusTower : ∀ k : ℕ,
      defectTower k
        (qgtPlus observerMatrixCut observerMatrixForward observerMatrixReverse) = 0 := by
    intro k
    induction k with
    | zero => simpa [defectTower, hPlus] using observer_matrix_reflexive_instance.1
    | succ k ih => simp [defectTower, idempotencyDefect, ih]
  have hMinusTower : ∀ k : ℕ,
      defectTower k
        (qgtMinus observerMatrixCut observerMatrixForward observerMatrixReverse) = 0 := by
    intro k
    induction k with
    | zero =>
        have hComplementDef : idempotencyDefect (1 - observerMatrixCut) = 0 := by
          unfold idempotencyDefect
          noncomm_ring [hCut]
        simpa [defectTower, hMinus] using hComplementDef
    | succ k ih => simp [defectTower, idempotencyDefect, ih]
  have hModel : ∀ k : ℕ,
      metaSelfModel k observerMatrixCut observerMatrixForward observerMatrixReverse =
        observerMatrixCut := by
    intro k
    unfold metaSelfModel metaSig
    rw [hPlusTower k, hMinusTower k]
    simp
  refine ⟨hPlusTower n, hMinusTower n, ?_, ?_, hModel n, ?_, hModel (n + 1)⟩
  · simp [metaV, hPlusTower n, hMinusTower n]
  · simp [metaSig, hPlusTower n, hMinusTower n]
  · rw [hModel n]
    exact observer_matrix_reflexive_instance.1

/-- A doubled forward matrix unit gives a nonzero, nonterminating tower in
the same noncommuting operator carrier. The metric remains `2 • 1`, while the
self-model is a fixed point of the autonomous recurrence. -/
def observerMatrixForwardDouble : ObserverMatrix :=
  (2 : ℤ) • observerMatrixForward

theorem observer_matrix_nontrivial_meta_reflection_fixed_point (n : ℕ) :
    observerMatrixForwardDouble * observerMatrixReverse ≠
      observerMatrixReverse * observerMatrixForwardDouble ∧
    defectTower n
        (qgtPlus observerMatrixCut observerMatrixForwardDouble observerMatrixReverse) =
      (2 : ℤ) • observerMatrixCut ∧
    defectTower n
        (qgtMinus observerMatrixCut observerMatrixForwardDouble observerMatrixReverse) =
      (2 : ℤ) • (1 - observerMatrixCut) ∧
    metaV n observerMatrixCut observerMatrixForwardDouble observerMatrixReverse =
      (2 : ℤ) • (1 : ObserverMatrix) ∧
    metaSig n observerMatrixCut observerMatrixForwardDouble observerMatrixReverse =
      (2 : ℤ) • invS observerMatrixCut ∧
    metaSelfModel n observerMatrixCut observerMatrixForwardDouble observerMatrixReverse =
      observerMatrixCut - (2 : ℤ) • invS observerMatrixCut ∧
    idempotencyDefect (metaSelfModel n observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse) = (2 : ℤ) • (1 : ObserverMatrix) ∧
    idempotencyDefect (metaSelfModel n observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse) ≠ 0 ∧
    metaSelfModel (n + 1) observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse =
      observerMatrixCut - invS observerMatrixCut *
        idempotencyDefect (metaSelfModel n observerMatrixCut observerMatrixForwardDouble
          observerMatrixReverse) ∧
    metaSelfModel (n + 1) observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse =
    metaSelfModel n observerMatrixCut observerMatrixForwardDouble observerMatrixReverse := by
  have hPlus : qgtPlus observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse = (2 : ℤ) • observerMatrixCut := by
    decide
  have hMinus : qgtMinus observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse = (2 : ℤ) • (1 - observerMatrixCut) := by
    decide
  have hPlusDef : idempotencyDefect ((2 : ℤ) • observerMatrixCut) =
      (2 : ℤ) • observerMatrixCut := by
    decide
  have hMinusDef : idempotencyDefect ((2 : ℤ) • (1 - observerMatrixCut)) =
      (2 : ℤ) • (1 - observerMatrixCut) := by
    decide
  have hPlusTower : ∀ k : ℕ,
      defectTower k
        (qgtPlus observerMatrixCut observerMatrixForwardDouble observerMatrixReverse) =
          (2 : ℤ) • observerMatrixCut := by
    intro k
    induction k with
    | zero => simpa [defectTower, hPlus] using hPlusDef
    | succ k ih => simpa [defectTower, ih] using hPlusDef
  have hMinusTower : ∀ k : ℕ,
      defectTower k
        (qgtMinus observerMatrixCut observerMatrixForwardDouble observerMatrixReverse) =
          (2 : ℤ) • (1 - observerMatrixCut) := by
    intro k
    induction k with
    | zero => simpa [defectTower, hMinus] using hMinusDef
    | succ k ih => simpa [defectTower, ih] using hMinusDef
  have hMetric : ∀ k : ℕ,
      metaV k observerMatrixCut observerMatrixForwardDouble observerMatrixReverse =
        (2 : ℤ) • (1 : ObserverMatrix) := by
    intro k
    rw [metaV, hPlusTower k, hMinusTower k]
    noncomm_ring
  have hCurvature : ∀ k : ℕ,
      metaSig k observerMatrixCut observerMatrixForwardDouble observerMatrixReverse =
        (2 : ℤ) • invS observerMatrixCut := by
    intro k
    rw [metaSig, hPlusTower k, hMinusTower k]
    simp only [invS]
    noncomm_ring
  have hModel : ∀ k : ℕ,
      metaSelfModel k observerMatrixCut observerMatrixForwardDouble observerMatrixReverse =
        observerMatrixCut - (2 : ℤ) • invS observerMatrixCut := by
    intro k
    simp [metaSelfModel, hCurvature k]
  refine ⟨by decide, hPlusTower n, hMinusTower n, hMetric n, hCurvature n,
    hModel n, ?_, ?_, ?_, ?_⟩
  · rw [hModel n]
    decide
  · rw [hModel n]
    decide
  · rw [hModel (n + 1), hModel n]
    decide
  · rw [hModel (n + 1), hModel n]

/-- This concrete defect orbit never becomes zero: every finite depth has
metric `2 • 1` in `M₂(ℤ)`. Thus eventual-zero behavior is not a theorem of the
abstract ring hypotheses. -/
theorem observer_matrix_metric_tower_ne_zero (n : ℕ) :
    metaV n observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse ≠ 0 := by
  have hOrbit := observer_matrix_nontrivial_meta_reflection_fixed_point n
  have hMetric : metaV n observerMatrixCut observerMatrixForwardDouble
      observerMatrixReverse = (2 : ℤ) • (1 : ObserverMatrix) :=
    hOrbit.2.2.2.1
  rw [hMetric]
  decide

/-- On the free module `ℤ²`, the concrete idempotent and its complement split
every vector into two fixed components. This is the module-level Peirce
decomposition for the matrix realization above. -/
theorem observer_matrix_vector_peirce_split (x : Fin 2 → ℤ) :
    observerMatrixCut.mulVec x + (1 - observerMatrixCut).mulVec x = x ∧
    observerMatrixCut.mulVec (observerMatrixCut.mulVec x) =
      observerMatrixCut.mulVec x ∧
    (1 - observerMatrixCut).mulVec ((1 - observerMatrixCut).mulVec x) =
      (1 - observerMatrixCut).mulVec x := by
  have hCut : observerMatrixCut * observerMatrixCut = observerMatrixCut :=
    observer_matrix_peirce_cycles.1
  have hComplement : (1 - observerMatrixCut) * (1 - observerMatrixCut) =
      1 - observerMatrixCut := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hCut]
    abel
  have hSum : observerMatrixCut + (1 - observerMatrixCut) = 1 := by
    noncomm_ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.add_mulVec, hSum, Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec, hCut]
  · rw [Matrix.mulVec_mulVec, hComplement]

/-! ### A twisted Peirce boundary: corrected finite identities -/

/-- Conjugation by the Peirce grading involution. -/
def peirceGradingConj (P X : B) : B := invS P * X * invS P

/-- A degree-sensitive commutator expression used to test the proposed
obstruction-killing formulas. This definition alone does not assert a chain
complex or a Koszul--Tate resolution. -/
def peirceTwistedBoundary (P A C X : B) : B :=
  genPhi P A C * X - peirceGradingConj P X * genPhi P A C

/-- The two polynomial factors proposed as a Peirce modular pair. Their names
do not assert mutual invertibility. -/
def peirceModularFactor (P A C : B) : B :=
  genJ P A C + (1 - genV P A C)

def peirceModularPartner (P A C : B) : B :=
  -genJ P A C + (1 - genV P A C)

/-- Both ordered products equal `1 + δ(V)`; the pair is inverse only on the
idempotent locus of the Peirce metric. -/
theorem peirce_modular_pair_product {P : B} (hP : P * P = P)
    (A C : B) :
    peirceModularFactor P A C * peirceModularPartner P A C =
      1 + idempotencyDefect (genV P A C) ∧
    peirceModularPartner P A C * peirceModularFactor P A C =
      1 + idempotencyDefect (genV P A C) := by
  constructor <;>
    (unfold peirceModularFactor peirceModularPartner idempotencyDefect;
     peirce_nf hP)

/-- The proposed modular pair is genuinely two-sided inverse exactly when
`V` is idempotent. -/
theorem peirce_modular_pair_is_inverse_iff {P : B}
    (hP : P * P = P) (A C : B) :
    (peirceModularFactor P A C * peirceModularPartner P A C = 1 ∧
      peirceModularPartner P A C * peirceModularFactor P A C = 1) ↔
        idempotencyDefect (genV P A C) = 0 := by
  rcases peirce_modular_pair_product hP A C with ⟨hleft, hright⟩
  constructor
  · rintro ⟨h, _⟩
    rw [hleft] at h
    have h' : 1 + idempotencyDefect (genV P A C) = 1 + 0 := by simpa using h
    exact add_left_cancel h'
  · intro h
    exact ⟨by rw [hleft, h]; simp, by rw [hright, h]; simp⟩

/-- The square of the twisted boundary is the inner derivation generated by
the Peirce metric. Consequently this operator is not a differential on all
of `B` without an additional centrality condition on `genV`. -/
theorem peirce_twisted_boundary_square {P : B} (hP : P * P = P)
    (A C X : B) :
    peirceTwistedBoundary P A C
      (peirceTwistedBoundary P A C X) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genV P A C) X := by
  unfold peirceTwistedBoundary peirceGradingConj
  peirce_nf hP

/-- The twisted boundary squares to zero on every operator exactly when its
Peirce metric is central. This is the precise condition under which the
displayed operator is a differential on the whole ring. -/
theorem peirce_twisted_boundary_is_differential_iff_central_metric
    {P : B} (hP : P * P = P) (A C : B) :
    (∀ X : B,
      peirceTwistedBoundary P A C (peirceTwistedBoundary P A C X) = 0) ↔
      ∀ X : B, genV P A C * X = X * genV P A C := by
  constructor
  · intro h X
    have hComm := peirce_twisted_boundary_square hP A C X
    rw [h X] at hComm
    exact sub_eq_zero.mp hComm.symm
  · intro h X
    rw [peirce_twisted_boundary_square hP A C X]
    exact sub_eq_zero.mpr (h X)

/-- Exact values of the twisted boundary on the Peirce generators. In
particular, the base idempotent is not closed: its image is `-J`. -/
theorem peirce_twisted_boundary_generator_values {P : B}
    (hP : P * P = P) (A C : B) :
    peirceTwistedBoundary P A C 1 = 0 ∧
    peirceTwistedBoundary P A C P = -genJ P A C ∧
    peirceTwistedBoundary P A C (genV P A C) = 0 ∧
    peirceTwistedBoundary P A C (genPhi P A C) = (2 : ℤ) • genV P A C ∧
    peirceTwistedBoundary P A C
      (peirceTwistedBoundary P A C (genPhi P A C)) = 0 := by
  have hPhi : peirceTwistedBoundary P A C (genPhi P A C) =
      (2 : ℤ) • genV P A C := by
    unfold peirceTwistedBoundary peirceGradingConj
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold peirceTwistedBoundary peirceGradingConj
    peirce_nf hP
  · unfold peirceTwistedBoundary peirceGradingConj
    peirce_nf hP
  · unfold peirceTwistedBoundary peirceGradingConj
    peirce_nf hP
  · exact hPhi
  · rw [hPhi]
    unfold peirceTwistedBoundary peirceGradingConj
    peirce_nf hP

/-- The centralizer of a fixed operator is closed under the ambient ring
commutator. No idempotency assumption is needed for this algebraic fact. -/
theorem cut_centralizer_closed_under_commutator {P K₁ K₂ : B}
    (hK₁ : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P K₁ = 0)
    (hK₂ : InfoGeometry.OperatorAlgebra.PeirceSpine.comm P K₂ = 0) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm K₁ P = 0 ∧
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm K₁ K₂) = 0 := by
  have h₁ : P * K₁ = K₁ * P := sub_eq_zero.mp hK₁
  have h₂ : P * K₂ = K₂ * P := sub_eq_zero.mp hK₂
  constructor
  · unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [← h₁]
    exact sub_self _
  · have h₁₂ : P * (K₁ * K₂) = (K₁ * K₂) * P := by
      calc
        P * (K₁ * K₂) = (P * K₁) * K₂ := by rw [← mul_assoc]
        _ = (K₁ * P) * K₂ := by rw [h₁]
        _ = K₁ * (P * K₂) := by rw [mul_assoc]
        _ = K₁ * (K₂ * P) := by rw [h₂]
        _ = (K₁ * K₂) * P := by rw [← mul_assoc]
    have h₂₁ : P * (K₂ * K₁) = (K₂ * K₁) * P := by
      calc
        P * (K₂ * K₁) = (P * K₂) * K₁ := by rw [← mul_assoc]
        _ = (K₂ * P) * K₁ := by rw [h₂]
        _ = K₂ * (P * K₁) := by rw [mul_assoc]
        _ = K₂ * (K₁ * P) := by rw [h₁]
        _ = (K₂ * K₁) * P := by rw [← mul_assoc]
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    simp only [mul_sub, sub_mul, h₁₂, h₂₁]
    abel

end InfoGeometry.PureOperatorConsciousness

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceLogisticBitwordBridge
import InfoGeometry.Canonical.ChiralCuntzAnomalyPartitionBridge
import InfoGeometry.Meta.ArchetypePipeline

/-!
# D₆₃ algebraic horizon identities

This module assembles Peirce corner identities for trace balance, invariance
under diagonal parameter changes, logistic-state impurity, mirror sandwiches,
and a two-sided inverse for a product of square-zero shears. These are ring
theorems; no entropy, geometric area, decoding protocol, time evolution, or
physical unitarity is defined here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.MetaCompiler

variable {B : Type*} [Ring B]

/-- A Peirce cut with idempotency carried intrinsically in the input type. -/
abbrev BH63IdempotentCut (B : Type*) [Ring B] := {P : B // P * P = P}

/-! ## Sheet trace balance and diagonal parameter invariance -/

theorem peirce_sheet_trace_balance
    (τ : B → R) [Ring R]
    (hAdd : ∀ X Y : B, τ (X + Y) = τ X + τ Y)
    (hSub : ∀ X Y : B, τ (X - Y) = τ X - τ Y)
    (hCyc : ∀ X Y : B, τ (X * Y) = τ (Y * X))
    {P : B} (A C : B) :
    τ (qgtPlus P A C) = τ (qgtMinus P A C) ∧
    τ (genSig P A C) = 0 ∧
    τ (genV P A C) = (2 : ℤ) • τ (qgtMinus P A C) ∧
    τ (genV P A C) = (2 : ℤ) • τ (qgtPlus P A C) := by
  have hSheets : τ (qgtPlus P A C) = τ (qgtMinus P A C) := by
    change τ (conePlus P A * coneMinus P C) =
      τ (coneMinus P C * conePlus P A)
    exact hCyc (conePlus P A) (coneMinus P C)
  have hMetricMinus : τ (genV P A C) =
      (2 : ℤ) • τ (qgtMinus P A C) := by
    change τ (qgtPlus P A C + qgtMinus P A C) =
      (2 : ℤ) • τ (qgtMinus P A C)
    rw [hAdd, hSheets, ← two_zsmul]
  refine ⟨hSheets, ?_, hMetricMinus, ?_⟩
  · change τ (qgtPlus P A C - qgtMinus P A C) = 0
    rw [hSub, hSheets, sub_self]
  · rw [hMetricMinus, hSheets]

/-! ## Proof-carrying sheet-balance archetype -/

/-- A ring-valued additive cyclic trace together with the two amplitudes whose
Peirce sheets are being compared. The trace laws are explicit input data. -/
structure BH63TraceBalanceInput (B R : Type*) [Ring B] [Ring R] where
  cut : BH63IdempotentCut B
  trace : InfoGeometry.Canonical.ChiralCuntzAnomalyPartitionBridge.CyclicTrace B R
  forwardAmplitude : B
  backwardAmplitude : B

/-- Cyclicity identifies the two ordered Peirce sheets and their metric traces.
This is conditional on the stated additive and cyclic trace laws. -/
def bh63TraceBalanceArchetype {B R : Type*} [Ring B] [Ring R] :
    TypedArchetype (BH63TraceBalanceInput B R) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation.bh63TraceBalanceArchetype
  phase := 63
  claim := fun input =>
    let τ := input.trace.toFun
    let P := (input.cut : B)
    let A := input.forwardAmplitude
    let C := input.backwardAmplitude
    τ (qgtPlus P A C) = τ (qgtMinus P A C) ∧
      τ (genSig P A C) = 0 ∧
      τ (genV P A C) = (2 : ℤ) • τ (qgtMinus P A C) ∧
      τ (genV P A C) = (2 : ℤ) • τ (qgtPlus P A C)
  evidence := fun input => peirce_sheet_trace_balance (P := (input.cut : B))
    input.trace.toFun
    (fun X Y => input.trace.toFun.map_add X Y)
    (fun X Y => input.trace.toFun.map_sub X Y)
    input.trace.cyclic input.forwardAmplitude input.backwardAmplitude

theorem peirce_logistic_state_eq_cut_sub_curvature
    {P : B} (hP : P * P = P) (A C : B) :
    peirceLogisticPlus P A C = P - genSig P A C := by
  unfold peirceLogisticPlus qgtPlus qgtMinus genSig comm conePlus coneMinus
  peirce_nf hP

/-- The Page-state expression in Peirce-corner form. -/
def pageDensityOp (P A C : B) : B :=
  P * (1 - qgtPlus P A C) + (1 - P) * qgtMinus P A C

/-- The algebraic impurity associated with the Page-state expression. -/
def pageImpurity (P A C : B) : B :=
  pageDensityOp P A C * (1 - pageDensityOp P A C)

theorem page_density_eq_cut_sub_curvature
    {P : B} (hP : P * P = P) (A C : B) :
    pageDensityOp P A C = P - genSig P A C := by
  unfold pageDensityOp qgtPlus qgtMinus genSig comm conePlus coneMinus
  peirce_nf hP

theorem peirce_metric_curvature_invariant_under_even_changes
    {P : B} (hP : P * P = P) (A C U W : B) :
    genV P (A + evenGrade P U) (C + evenGrade P W) = genV P A C ∧
    genSig P (A + evenGrade P U) (C + evenGrade P W) = genSig P A C := by
  have hUpper : conePlus P (evenGrade P U) = 0 := by
    unfold conePlus evenGrade
    peirce_nf hP
  have hLower : coneMinus P (evenGrade P W) = 0 := by
    unfold coneMinus evenGrade
    peirce_nf hP
  unfold genV genSig
  simp only [conePlus_add, coneMinus_add, hUpper, hLower]
  simp [anticomm, comm]

/-! ## Proof-carrying bulk-invariance archetype -/

/-- Data for invariance of the two transition-sheet operators under diagonal
Peirce perturbations of their amplitudes. -/
structure BH63BulkInvarianceInput (B : Type*) [Ring B] where
  cut : BH63IdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B
  interiorPerturbation : B
  exteriorPerturbation : B

/-- Diagonal Peirce perturbations leave the metric and curvature operators
unchanged. The archetype is discharged by the owner theorem above. -/
def bh63BulkInvarianceArchetype {B : Type*} [Ring B] :
    TypedArchetype (BH63BulkInvarianceInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation.bh63BulkInvarianceArchetype
  phase := 63
  claim := fun input =>
    genV (input.cut : B)
        (input.forwardAmplitude + evenGrade (input.cut : B) input.interiorPerturbation)
        (input.backwardAmplitude + evenGrade (input.cut : B) input.exteriorPerturbation) =
      genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude ∧
    genSig (input.cut : B)
        (input.forwardAmplitude + evenGrade (input.cut : B) input.interiorPerturbation)
        (input.backwardAmplitude + evenGrade (input.cut : B) input.exteriorPerturbation) =
      genSig (input.cut : B) input.forwardAmplitude input.backwardAmplitude
  evidence := fun input => peirce_metric_curvature_invariant_under_even_changes
    input.cut.property input.forwardAmplitude input.backwardAmplitude
      input.interiorPerturbation input.exteriorPerturbation

/-! ## Logistic-state impurity -/

theorem logistic_state_page_impurity
    {P : B} [StarRing B] (hP : P * P = P) (A C : B) :
    peirceLogisticPlus P A C * (1 - peirceLogisticPlus P A C) =
      -(genV P A C * genV P A C - genV P A C) ∧
    (peirceLogisticPlus P A C * peirceLogisticPlus P A C =
        peirceLogisticPlus P A C ↔
      genV P A C * genV P A C - genV P A C = 0) := by
  rcases peirceLogistic_operator_identities hP A C with
    ⟨_, hComplement, hProduct, _⟩
  have hImpurity : peirceLogisticPlus P A C *
      (1 - peirceLogisticPlus P A C) =
      -(genV P A C * genV P A C - genV P A C) := by
    rw [hComplement]
    exact hProduct
  have hDefect : peirceLogisticPlus P A C * peirceLogisticPlus P A C -
      peirceLogisticPlus P A C = genV P A C * genV P A C - genV P A C := by
    calc
      peirceLogisticPlus P A C * peirceLogisticPlus P A C -
          peirceLogisticPlus P A C =
          -(peirceLogisticPlus P A C *
            (1 - peirceLogisticPlus P A C)) := by noncomm_ring
      _ = genV P A C * genV P A C - genV P A C := by
        rw [hImpurity]
        simp
  refine ⟨hImpurity, ?_⟩
  constructor
  · intro h
    have hzero : peirceLogisticPlus P A C * peirceLogisticPlus P A C -
        peirceLogisticPlus P A C = 0 := sub_eq_zero.mpr h
    rw [hDefect] at hzero
    exact hzero
  · intro h
    have hzero : peirceLogisticPlus P A C * peirceLogisticPlus P A C -
        peirceLogisticPlus P A C = 0 := by rw [hDefect, h]
    exact sub_eq_zero.mp hzero

theorem page_impurity_eq_negative_metric_defect
    {P : B} [StarRing B] (hP : P * P = P) (A C : B) :
    pageImpurity P A C = -(genV P A C * genV P A C - genV P A C) := by
  unfold pageImpurity
  change peirceLogisticPlus P A C * (1 - peirceLogisticPlus P A C) = _
  exact (logistic_state_page_impurity hP A C).1

/-! ## Proof-carrying Page-defect archetype -/


/-- Input carrier for the Page-state defect archetype. -/
structure BH63PageDefectInput (B : Type*) [Ring B] [StarRing B] where
  cut : BH63IdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B

/-- The Page-state impurity equals the negative logistic defect.  This typed
archetype records the exact algebraic theorem proved above. -/
def bh63PageDefectArchetype {B : Type*} [Ring B] [StarRing B] :
    TypedArchetype (BH63PageDefectInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation.bh63PageDefectArchetype
  phase := 63
  claim := fun input =>
    pageImpurity (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      -(genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude -
        genV (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
  evidence := fun input => page_impurity_eq_negative_metric_defect
    input.cut.property input.forwardAmplitude input.backwardAmplitude

/-- Data for the exact two-sided Peirce-shear inverse statement. -/
structure BH63ShearInput (B : Type*) [Ring B] where
  cut : BH63IdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B

/-- The Page impurity is exactly the ordered product of the complementary
Peirce logistic coordinates `L₊` and `L₋`. -/
theorem page_impurity_eq_logistic_pair
    {P : B} [StarRing B] (hP : P * P = P) (A C : B) :
    1 - peirceLogisticPlus P A C = peirceLogisticMinus P A C ∧
    pageImpurity P A C =
      peirceLogisticPlus P A C * peirceLogisticMinus P A C := by
  rcases peirceLogistic_operator_identities hP A C with
    ⟨_, hComplement, _, _⟩
  have hDensity : pageDensityOp P A C = peirceLogisticPlus P A C := by
    rw [page_density_eq_cut_sub_curvature hP A C,
      peirce_logistic_state_eq_cut_sub_curvature hP A C]
  constructor
  · exact hComplement
  · calc
      pageImpurity P A C = peirceLogisticPlus P A C *
          (1 - peirceLogisticPlus P A C) := by
            unfold pageImpurity
            rw [hDensity]
      _ = peirceLogisticPlus P A C * peirceLogisticMinus P A C := by
            rw [hComplement]

/-- Page-state purity and vanishing impurity are both equivalent to the
idempotency of the Peirce metric. -/
theorem page_purity_iff_metric_idempotency_defect
    {P : B} [StarRing B] (hP : P * P = P) (A C : B) :
    (pageDensityOp P A C * pageDensityOp P A C = pageDensityOp P A C ↔
      genV P A C * genV P A C - genV P A C = 0) ∧
    (pageImpurity P A C = 0 ↔
      genV P A C * genV P A C - genV P A C = 0) := by
  have hDensity : pageDensityOp P A C = peirceLogisticPlus P A C := by
    rw [page_density_eq_cut_sub_curvature hP A C,
      peirce_logistic_state_eq_cut_sub_curvature hP A C]
  have hPure := (logistic_state_page_impurity hP A C).2
  have hImpurity := page_impurity_eq_negative_metric_defect hP A C
  constructor
  · rw [hDensity]
    exact hPure
  · constructor
    · intro hzero
      rw [hImpurity] at hzero
      exact neg_eq_zero.mp hzero
    · intro hdefect
      rw [hImpurity, hdefect]
      simp

theorem logistic_state_at_zero_upper_corner
    {P : B} [StarRing B] (hP : P * P = P) (C : B) :
    peirceLogisticPlus P 0 C = P ∧
    peirceLogisticPlus P 0 C * (1 - peirceLogisticPlus P 0 C) = 0 := by
  have hState : peirceLogisticPlus P 0 C = P := by
    unfold peirceLogisticPlus qgtPlus qgtMinus conePlus
    peirce_nf hP
  refine ⟨hState, ?_⟩
  rw [hState]
  noncomm_ring [hP]

/-! ## Mirror maps and sheet reconstruction -/

def peirceMirrorMap (P A C X : B) : B :=
  conePlus P A * X * conePlus P A + coneMinus P C * X * coneMinus P C

theorem peirce_mirror_and_sheet_sandwiches
    {P : B} (hP : P * P = P) (A C : B) :
    peirceMirrorMap P A C (conePlus P A) =
      coneMinus P C * genV P A C ∧
    peirceMirrorMap P A C (coneMinus P C) =
      genV P A C * conePlus P A ∧
    genPhi P A C * qgtMinus P A C * genPhi P A C =
      qgtPlus P A C * qgtPlus P A C ∧
    genPhi P A C * qgtPlus P A C * genPhi P A C =
      qgtMinus P A C * qgtMinus P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirceMirrorMap, genPhi, genV, anticomm, qgtPlus,
      qgtMinus, conePlus, coneMinus]; peirce_nf hP)

/-! ## Proof-carrying mirror-sandwich archetype -/

/-- Data for the exact two-sheet mirror-sandwich identities. -/
structure BH63MirrorSandwichInput (B : Type*) [Ring B] where
  cut : BH63IdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B

/-- The transition operator exchanges the two ordered sheets by sandwiching;
the result is the square of the target sheet, with no idempotency assumption
on either sheet. -/
def bh63MirrorSandwichArchetype {B : Type*} [Ring B] :
    TypedArchetype (BH63MirrorSandwichInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation.bh63MirrorSandwichArchetype
  phase := 63
  claim := fun input =>
    genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude ∧
    genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude
  evidence := fun input => by
    rcases peirce_mirror_and_sheet_sandwiches input.cut.property
        input.forwardAmplitude input.backwardAmplitude with
      ⟨_, _, hInterior, hExterior⟩
    exact ⟨hInterior, hExterior⟩

/-- The two-sided sheet sandwich recovers a sheet itself exactly when that
sheet is idempotent. Without this condition, the sandwich theorem returns
the square of the sheet. -/
theorem peirce_sheet_sandwich_recovers_sheet_iff_idempotent
    {P : B} (hP : P * P = P) (A C : B) :
    (genPhi P A C * qgtMinus P A C * genPhi P A C = qgtPlus P A C ↔
      qgtPlus P A C * qgtPlus P A C = qgtPlus P A C) ∧
    (genPhi P A C * qgtPlus P A C * genPhi P A C = qgtMinus P A C ↔
      qgtMinus P A C * qgtMinus P A C = qgtMinus P A C) := by
  rcases peirce_mirror_and_sheet_sandwiches hP A C with
    ⟨_, _, hInterior, hExterior⟩
  constructor
  · rw [hInterior]
  · rw [hExterior]

/-- Carrier for the sheet-recovery criterion, with cut idempotency intrinsic
to the input. -/
structure BH63SheetRecoveryInput (B : Type*) [Ring B] where
  cut : BH63IdempotentCut B
  forwardAmplitude : B
  backwardAmplitude : B

/-- Exact recovery by a sheet sandwich is equivalent to idempotency of the
corresponding sheet. -/
def bh63SheetRecoveryCriterionArchetype {B : Type*} [Ring B] :
    TypedArchetype (BH63SheetRecoveryInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation.bh63SheetRecoveryCriterionArchetype
  phase := 63
  claim := fun input =>
    (genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude ↔
      qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude) ∧
    (genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtPlus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        genPhi (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude ↔
      qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude =
      qgtMinus (input.cut : B) input.forwardAmplitude input.backwardAmplitude)
  evidence := fun input => peirce_sheet_sandwich_recovers_sheet_iff_idempotent
    input.cut.property input.forwardAmplitude input.backwardAmplitude

/-! ## Two-sided invertibility of a product of Peirce shears -/

def horizonShear (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C)

def horizonShearInv (P A C : B) : B :=
  (1 + coneMinus P C) * (1 - conePlus P A)

theorem peirce_shear_two_sided_inverse
    {P : B} (hP : P * P = P) (A C : B) :
    horizonShear P A C * horizonShearInv P A C = 1 ∧
    horizonShearInv P A C * horizonShear P A C = 1 := by
  constructor <;>
    (simp only [horizonShear, horizonShearInv, conePlus, coneMinus];
      peirce_nf hP)

/-- The horizon shear is algebraically invertible with the displayed inverse.
This archetype asserts two-sided invertibility, not star-unitarity. -/
def bh63ShearReversibilityArchetype {B : Type*} [Ring B] :
    TypedArchetype (BH63ShearInput B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation.bh63ShearReversibilityArchetype
  phase := 63
  claim := fun input =>
    horizonShear (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        horizonShearInv (input.cut : B) input.forwardAmplitude input.backwardAmplitude = 1 ∧
      horizonShearInv (input.cut : B) input.forwardAmplitude input.backwardAmplitude *
        horizonShear (input.cut : B) input.forwardAmplitude input.backwardAmplitude = 1
  evidence := fun input => peirce_shear_two_sided_inverse
    input.cut.property input.forwardAmplitude input.backwardAmplitude

theorem peirce_shear_conjugation_recovery
    {P : B} (hP : P * P = P) (A C X : B) :
    horizonShearInv P A C *
      (horizonShear P A C * X * horizonShearInv P A C) *
      horizonShear P A C = X := by
  rcases peirce_shear_two_sided_inverse hP A C with ⟨hLeft, hRight⟩
  calc
    _ = (horizonShearInv P A C * horizonShear P A C) * X *
        (horizonShearInv P A C * horizonShear P A C) := by noncomm_ring
    _ = X := by rw [hRight, one_mul, mul_one]

/-- Lossless conjugation by a Peirce shear, packaged as an archetype for each
idempotent cut, pair of amplitudes, and operator state.  Its evidence is the
two-sided inverse theorem above, rather than an assumed recovery law. -/
def bh63ShearConjugationRecoveryArchetype {B : Type*} [Ring B] :
    TypedArchetype (BH63ShearInput B × B) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation.bh63ShearConjugationRecoveryArchetype
  phase := 63
  claim := fun input =>
    horizonShearInv (input.1.cut : B) input.1.forwardAmplitude input.1.backwardAmplitude *
      (horizonShear (input.1.cut : B) input.1.forwardAmplitude input.1.backwardAmplitude *
        input.2 *
       horizonShearInv (input.1.cut : B) input.1.forwardAmplitude input.1.backwardAmplitude) *
      horizonShear (input.1.cut : B) input.1.forwardAmplitude input.1.backwardAmplitude = input.2
  evidence := fun input => peirce_shear_conjugation_recovery
    input.1.cut.property input.1.forwardAmplitude input.1.backwardAmplitude input.2

/-! ## Proof-backed causal poset of the D₆₃ archetypes

Only theorem-level dependencies are edges. Input strata such as “operator
data”, idempotency, and trace laws are not presented as theorem conclusions.
The two edges below are propositions asserting the complete downstream
archetype claims, discharged by their owner evidence.
-/

inductive BH63Stage (B : Type*) [Ring B] [StarRing B] where
  | traceBalance
  | bulkInvariance
  | pageDefect
  | mirrorSandwiches
  | sheetRecoveryCriterion
  | shearReversibility
  | stateConjugationRecovery
  deriving DecidableEq, Repr

/-- A direct edge records the exact proof obligation of its target archetype. -/
def BH63Stage.edge {B : Type*} [Ring B] [StarRing B] :
    BH63Stage B → BH63Stage B → Prop
  | .mirrorSandwiches, .sheetRecoveryCriterion =>
      ∀ input : BH63SheetRecoveryInput B,
        bh63SheetRecoveryCriterionArchetype.claim input
  | .shearReversibility, .stateConjugationRecovery =>
      ∀ input : BH63ShearInput B × B,
        bh63ShearConjugationRecoveryArchetype.claim input
  | _, _ => False

inductive BH63Stage.Reachable {B : Type*} [Ring B] [StarRing B] :
    BH63Stage B → BH63Stage B → Prop where
  | refl (a : BH63Stage B) : Reachable a a
  | edge {a b : BH63Stage B} : a.edge b → Reachable a b
  | trans {a b c : BH63Stage B} : Reachable a b → Reachable b c → Reachable a c

def BH63Stage.dependencyLE {B : Type*} [Ring B] [StarRing B] :
    BH63Stage B → BH63Stage B → Prop := Reachable

def BH63Stage.rank {B : Type*} [Ring B] [StarRing B] : BH63Stage B → Nat
  | .traceBalance => 0
  | .bulkInvariance => 0
  | .pageDefect => 0
  | .mirrorSandwiches => 0
  | .shearReversibility => 0
  | .sheetRecoveryCriterion => 1
  | .stateConjugationRecovery => 1

theorem BH63Stage.edge_rank_strict {B : Type*} [Ring B] [StarRing B]
    {a b : BH63Stage B} (h : a.edge b) : a.rank < b.rank := by
  cases a <;> cases b <;> simp [edge, rank] at h ⊢

theorem BH63Stage.reachable_rank_strict_of_ne {B : Type*} [Ring B] [StarRing B]
    {a b : BH63Stage B} (h : a.Reachable b) (hne : a ≠ b) : a.rank < b.rank := by
  induction h with
  | @refl x => exact (hne rfl).elim
  | edge h => exact edge_rank_strict h
  | @trans x y z hxy hyz ihxy ihyz =>
      by_cases hxyEq : x = y
      · subst y
        exact ihyz hne
      · by_cases hyzEq : y = z
        · subst z
          exact ihxy hne
        · exact lt_trans (ihxy hxyEq) (ihyz hyzEq)

theorem BH63Stage.dependencyLE_refl {B : Type*} [Ring B] [StarRing B]
    (a : BH63Stage B) : a.dependencyLE a := Reachable.refl a

theorem BH63Stage.dependencyLE_trans {B : Type*} [Ring B] [StarRing B]
    {a b c : BH63Stage B} (hab : a.dependencyLE b) (hbc : b.dependencyLE c) :
    a.dependencyLE c := Reachable.trans hab hbc

theorem BH63Stage.dependencyLE_antisymm {B : Type*} [Ring B] [StarRing B]
    {a b : BH63Stage B} (hab : a.dependencyLE b) (hba : b.dependencyLE a) : a = b := by
  by_cases hEq : a = b
  · exact hEq
  · exact (lt_asymm (reachable_rank_strict_of_ne hab hEq)
      (reachable_rank_strict_of_ne hba (Ne.symm hEq))).elim

instance {B : Type*} [Ring B] [StarRing B] : PartialOrder (BH63Stage B) where
  le := BH63Stage.dependencyLE
  le_refl := BH63Stage.dependencyLE_refl
  le_trans := fun _ _ _ hab hbc => BH63Stage.dependencyLE_trans hab hbc
  le_antisymm := fun _ _ hab hba => BH63Stage.dependencyLE_antisymm hab hba

theorem mirror_sandwich_precedes_sheet_recovery {B : Type*} [Ring B] [StarRing B] :
    BH63Stage.mirrorSandwiches (B := B) ≤
      BH63Stage.sheetRecoveryCriterion (B := B) := by
  apply BH63Stage.Reachable.edge
  intro input
  exact (bh63SheetRecoveryCriterionArchetype (B := B)).evidence input

theorem shear_reversibility_precedes_state_recovery {B : Type*} [Ring B] [StarRing B] :
    BH63Stage.shearReversibility (B := B) ≤
      BH63Stage.stateConjugationRecovery (B := B) := by
  apply BH63Stage.Reachable.edge
  intro input
  exact (bh63ShearConjugationRecoveryArchetype (B := B)).evidence input

/-! ## D₆₃ synthesis -/

theorem stage_D63_black_hole_peirce_master
    (τ : B → R) [Ring R]
    (hAdd : ∀ X Y : B, τ (X + Y) = τ X + τ Y)
    (hSub : ∀ X Y : B, τ (X - Y) = τ X - τ Y)
    (hCyc : ∀ X Y : B, τ (X * Y) = τ (Y * X))
    {P : B} (hP : P * P = P) (A C U W X : B) [StarRing B] :
    τ (qgtPlus P A C) = τ (qgtMinus P A C) ∧
    τ (genSig P A C) = 0 ∧
    τ (genV P A C) = (2 : ℤ) • τ (qgtPlus P A C) ∧
    τ (genV P A C) = (2 : ℤ) • τ (qgtMinus P A C) ∧
    genV P (A + evenGrade P U) (C + evenGrade P W) = genV P A C ∧
    genSig P (A + evenGrade P U) (C + evenGrade P W) = genSig P A C ∧
    peirceLogisticPlus P A C = P - genSig P A C ∧
    peirceLogisticPlus P 0 C = P ∧
    peirceLogisticPlus P 0 C * (1 - peirceLogisticPlus P 0 C) = 0 ∧
    peirceLogisticPlus P A C * (1 - peirceLogisticPlus P A C) =
      -(genV P A C * genV P A C - genV P A C) ∧
    (peirceLogisticPlus P A C * peirceLogisticPlus P A C =
        peirceLogisticPlus P A C ↔
      genV P A C * genV P A C - genV P A C = 0) ∧
    pageDensityOp P A C = P - genSig P A C ∧
    pageImpurity P A C = -(genV P A C * genV P A C - genV P A C) ∧
    (pageDensityOp P A C * pageDensityOp P A C = pageDensityOp P A C ↔
      genV P A C * genV P A C - genV P A C = 0) ∧
    (pageImpurity P A C = 0 ↔
      genV P A C * genV P A C - genV P A C = 0) ∧
    1 - peirceLogisticPlus P A C = peirceLogisticMinus P A C ∧
    pageImpurity P A C =
      peirceLogisticPlus P A C * peirceLogisticMinus P A C ∧
    genPhi P A C * qgtMinus P A C * genPhi P A C =
      qgtPlus P A C * qgtPlus P A C ∧
    genPhi P A C * qgtPlus P A C * genPhi P A C =
      qgtMinus P A C * qgtMinus P A C ∧
    peirceMirrorMap P A C (conePlus P A) =
      coneMinus P C * genV P A C ∧
    peirceMirrorMap P A C (coneMinus P C) =
      genV P A C * conePlus P A ∧
    horizonShear P A C * horizonShearInv P A C = 1 ∧
    horizonShearInv P A C * horizonShear P A C = 1 ∧
    horizonShearInv P A C *
      (horizonShear P A C * X * horizonShearInv P A C) *
      horizonShear P A C = X := by
  rcases peirce_sheet_trace_balance τ hAdd hSub hCyc A C with
    ⟨hTrace, hTraceSig, hMetricMinus, hMetricPlus⟩
  rcases peirce_metric_curvature_invariant_under_even_changes hP A C U W with
    ⟨hBulkV, hBulkSig⟩
  rcases logistic_state_page_impurity hP A C with ⟨hPage, hPure⟩
  rcases logistic_state_at_zero_upper_corner hP C with ⟨hInitial, hInitialPure⟩
  have hDensity := page_density_eq_cut_sub_curvature hP A C
  have hPageDefect := page_impurity_eq_negative_metric_defect hP A C
  rcases page_purity_iff_metric_idempotency_defect hP A C with
    ⟨hPagePure, hPageZero⟩
  rcases page_impurity_eq_logistic_pair hP A C with ⟨hLComplement, hLProduct⟩
  rcases peirce_mirror_and_sheet_sandwiches hP A C with
    ⟨hMirrorNPlus, hMirrorNMinus, hMirror1, hMirror2⟩
  rcases peirce_shear_two_sided_inverse hP A C with ⟨hInv1, hInv2⟩
  have hRecover := peirce_shear_conjugation_recovery hP A C X
  exact ⟨hTrace, hTraceSig, hMetricPlus, hMetricMinus, hBulkV, hBulkSig,
    peirce_logistic_state_eq_cut_sub_curvature hP A C,
    hInitial, hInitialPure, hPage, hPure, hDensity, hPageDefect,
    hPagePure, hPageZero,
    hLComplement, hLProduct,
    hMirror1, hMirror2,
    hMirrorNPlus, hMirrorNMinus, hInv1, hInv2, hRecover⟩

#register_archetype bh63TraceBalanceArchetype
#audit_archetype bh63TraceBalanceArchetype
#register_archetype bh63PageDefectArchetype
#audit_archetype bh63PageDefectArchetype
#register_archetype bh63BulkInvarianceArchetype
#audit_archetype bh63BulkInvarianceArchetype
#register_archetype bh63MirrorSandwichArchetype
#audit_archetype bh63MirrorSandwichArchetype
#register_archetype bh63SheetRecoveryCriterionArchetype
#audit_archetype bh63SheetRecoveryCriterionArchetype
#register_archetype bh63ShearReversibilityArchetype
#audit_archetype bh63ShearReversibilityArchetype
#register_archetype bh63ShearConjugationRecoveryArchetype
#audit_archetype bh63ShearConjugationRecoveryArchetype

end InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation

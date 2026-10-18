/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Order.Hom.Basic
import InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis
import InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis
import InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis

/-!
# Evidence-supported bridge poset for the inevitability synthesis

This finite partial order on proof-artifact labels is generated only by the
representation bridges and propagation statements listed in `EvidenceEdge`.
Edge direction records the selected bridge orientation; equality or
representation edges do not assert logical prerequisite dependence. It is not
an automatically extracted Lean declaration graph, a physical causality claim,
or a forced linear ordering of the five synthesis sections. Components without
a stated bridge remain incomparable. In particular, the Fisher result and the
para-Kähler null-sheet isotropy result are independent; the Möbius quotient has
no edge to the UHF/KMS carrier.

`Reach` is the reflexive transitive closure of the proof-carrying direct edges.
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.CategoricalInevitabilityCausalPoset

open InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis
open InfoGeometry.Synthesis.Cl11ChiralVolumeNilpotentQuotientSynthesis
open InfoGeometry.Synthesis.MathlibCliffordUniversalLiftSynthesis
open InfoGeometry.Canonical.SuperGrassmannianManifold
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionGNSBridge
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-- Proof artifacts appearing in the selected dependency corridors. -/
inductive Artifact where
  | fisherClassification
  | universalCl11Cell
  | cl11MatrixUnit
  | cl11PeirceProjector
  | wittCreationBase
  | finiteJordanWigner
  | colimitJordanWigner
  | colimitMixedCAR
  | paraKahlerNullSheets
  | paraProjectorLaws
  | mobiusSetQuotient
  | mobiusCrossSheetPairingDescent
  | flowAndKMSBoundaryLemmas
  | crossStageKMSReadout
  | prunedStageReadoutAndAnchorBound
  | prunedCrossStageSinkBound
  deriving DecidableEq, Repr

instance : Inhabited Artifact :=
  ⟨.fisherClassification⟩

/-- Non-default canonical witness for `Artifact`. -/
def canonicalArtifact : Artifact :=
  .colimitJordanWigner

/-- Non-degeneracy witness for `Artifact`: `.colimitJordanWigner` is distinct from the
default `.fisherClassification` label. -/
theorem canonicalArtifact_ne_fisherClassification :
    canonicalArtifact ≠ .fisherClassification := by
  decide

/-- A direct bridge requires an exact owner theorem or definitional
construction equation as evidence. Quotient evidence below is stated for
universe-zero carriers; the imported owner theorem is more general. -/
inductive EvidenceEdge : Artifact → Artifact → Prop where
  | universalCell_to_matrixUnit
      (h : cl11MatrixAlgEquiv abstractNullPlus = !![(0 : ℝ), 1; 0, 0]) :
      EvidenceEdge .universalCl11Cell .cl11MatrixUnit
  | universalCell_to_peirce
      (h : abstractVacProj * abstractVacProj = abstractVacProj) :
      EvidenceEdge .universalCl11Cell .cl11PeirceProjector
  | matrixUnit_to_wittBase
      (h : (!![(0 : ℝ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
        InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase) :
      EvidenceEdge .cl11MatrixUnit .wittCreationBase
  | wittBase_to_finiteJW
      (h : ∀ (n : ℕ) (i : Fin n),
        InfoGeometry.Clifford.Cl11TensorTower.jwCreation n i =
          InfoGeometry.Clifford.Cl11TensorTower.jwStringWithBase
            InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase n i) :
      EvidenceEdge .wittCreationBase .finiteJordanWigner
  | finiteJW_to_colimitJW
      (h : ∀ (n : ℕ) (i : Fin n),
        colimitJWCreation n i =
          stageInjection n
            (complexifyRealMatrix
              (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n
                (InfoGeometry.Clifford.Cl11TensorTower.jwCreation n i)))) :
      EvidenceEdge .finiteJordanWigner .colimitJordanWigner
  | colimitJW_to_mixedCAR
      (h : ∀ (k : ℕ) (i j : Fin k),
        colimitJWAnnihilation k i * colimitJWCreation k j +
          colimitJWCreation k j * colimitJWAnnihilation k i =
            if i = j then 1 else 0) :
      EvidenceEdge .colimitJordanWigner .colimitMixedCAR
  | paraProjectors_to_mobiusQuotient
      (h : ∀ {V : Type} [AddCommGroup V] [Module ℝ V]
        {K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) (v : V),
        (Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorPlus K v) :
          MobiusInvolutionQuotient hC) =
          Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorMinus K (C v))) :
      EvidenceEdge .paraProjectorLaws .mobiusSetQuotient
  | mobiusQuotient_to_crossSheetPairing
      (h : ∀ {V : Type} [AddCommGroup V] [Module ℝ V]
        (g omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {K C : V →ₗ[ℝ] V}
        (_hK : ParaComplexStructure K) (hPK : ParaKahlerStructure g omega K)
        (hC : IsSheetSwapInvolution K C)
        (hC_iso : ∀ u w, g (C u) (C w) = g u w)
        (q : MobiusInvolutionQuotient hC),
        mobiusQuotientQuadratic g hC hC_iso q =
          2 * mobiusQuotientCrossSheetPairing g omega hPK hC hC_iso q) :
      EvidenceEdge .mobiusSetQuotient .mobiusCrossSheetPairingDescent
  | flowAndBoundary_to_crossStageReadout
      (h : ∀ {k n : ℕ} (hle : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
        (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ),
        (selectedStageColimitFunctional k (attentionStageDensity k logits β)
            (stageInjection n
              (rawMap hle
                (modularFlow logits β t
                  (complexifyRealMatrix A *
                    complexifyRealMatrix
                      (attentionDensityMatrix logits β * B *
                        attentionDensityMatrixInv logits β))))) =
          selectedStageColimitFunctional k (attentionStageDensity k logits β)
            (stageInjection k
              (complexifyRealMatrix A *
                complexifyRealMatrix
                  (attentionDensityMatrix logits β * B *
                    attentionDensityMatrixInv logits β)))) ∧
        (selectedStageColimitFunctional k (attentionStageDensity k logits β)
            (stageInjection k
              (complexifyRealMatrix A *
                complexifyRealMatrix
                  (attentionDensityMatrix logits β * B *
                    attentionDensityMatrixInv logits β))) =
          selectedStageColimitFunctional k (attentionStageDensity k logits β)
            (stageInjection k (complexifyRealMatrix (B * A)))) →
          selectedStageColimitFunctional k (attentionStageDensity k logits β)
            (stageInjection n
              (rawMap hle
                (modularFlow logits β t
                  (complexifyRealMatrix A *
                    complexifyRealMatrix
                      (attentionDensityMatrix logits β * B *
                        attentionDensityMatrixInv logits β))))) =
          selectedStageColimitFunctional k (attentionStageDensity k logits β)
            (stageInjection k (complexifyRealMatrix (B * A)))) :
      EvidenceEdge .flowAndKMSBoundaryLemmas .crossStageKMSReadout
  | prunedFacts_to_crossStageSinkBound
      (h : ∀ {k n : ℕ} (hle : k ≤ n) (pw : PrunedWeights (Fin (2 ^ k)))
        (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (anchor : Fin (2 ^ k))
        (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ),
        (selectedStageColimitFunctional k (prunedStageDensity k pw)
            (stageInjection k
              (modularFlow logits β t
                (complexifyRealMatrix (A.transpose * A)))) =
          selectedStageColimitFunctional k (prunedStageDensity k pw)
            (stageInjection k (complexifyRealMatrix (A.transpose * A))) ∧
          pw.weights anchor * (∑ j : Fin (2 ^ k), (A j anchor) ^ 2) ≤
            (selectedStageColimitFunctional k (prunedStageDensity k pw)
              (stageInjection k
                (complexifyRealMatrix (A.transpose * A)))).re) →
        pw.weights anchor * (∑ j : Fin (2 ^ k), (A j anchor) ^ 2) ≤
          (selectedStageColimitFunctional k (prunedStageDensity k pw)
            (stageInjection n
              (rawMap hle
                (modularFlow logits β t
                  (complexifyRealMatrix (A.transpose * A)))))).re) :
      EvidenceEdge .prunedStageReadoutAndAnchorBound .prunedCrossStageSinkBound

/-- The universal null generator has the concrete matrix image used as the JW
creation base. -/
theorem abstractNullPlus_matrix_eq_wittCreationBase :
    cl11MatrixAlgEquiv abstractNullPlus =
      InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase := by
  rw [cl11MatrixAlgEquiv_abstractNullPlus]
  rfl

theorem matrixUnit_eq_wittCreationBase :
    (!![(0 : ℝ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase := rfl

theorem jwCreation_eq_base_string (n : ℕ) (i : Fin n) :
    InfoGeometry.Clifford.Cl11TensorTower.jwCreation n i =
      InfoGeometry.Clifford.Cl11TensorTower.jwStringWithBase
        InfoGeometry.Clifford.Cl11TensorTower.wittCreationBase n i := rfl

theorem colimitJWCreation_eq_stageInjection (n : ℕ) (i : Fin n) :
    colimitJWCreation n i =
      stageInjection n
        (complexifyRealMatrix
          (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo n
            (InfoGeometry.Clifford.Cl11TensorTower.jwCreation n i))) := rfl

theorem paraProjectorQuotientCorridor
    {V : Type} [AddCommGroup V] [Module ℝ V]
    {K C : V →ₗ[ℝ] V} (hC : IsSheetSwapInvolution K C) (v : V) :
    (Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorPlus K v) :
      MobiusInvolutionQuotient hC) =
      Quotient.mk (mobiusInvolutionSetoid hC) (paraProjectorMinus K (C v)) :=
  paraProjectorPlus_eq_paraProjectorMinus_in_mobiusQuotient hC v

/-- Height is used only to certify acyclicity of the selected edge graph. -/
def height : Artifact → ℕ
  | .fisherClassification => 0
  | .universalCl11Cell => 1
  | .cl11MatrixUnit => 5
  | .cl11PeirceProjector => 6
  | .wittCreationBase => 8
  | .finiteJordanWigner => 9
  | .colimitJordanWigner => 11
  | .colimitMixedCAR => 16
  | .paraKahlerNullSheets => 2
  | .paraProjectorLaws => 3
  | .mobiusSetQuotient => 7
  | .mobiusCrossSheetPairingDescent => 17
  | .flowAndKMSBoundaryLemmas => 12
  | .crossStageKMSReadout => 13
  | .prunedStageReadoutAndAnchorBound => 14
  | .prunedCrossStageSinkBound => 15

theorem height_injective : Function.Injective height := by
  intro a b h
  cases a <;> cases b <;> simp [height] at h ⊢

theorem height_lt_of_edge {a b : Artifact} (h : EvidenceEdge a b) :
    height a < height b := by
  cases h <;> decide

/-- Reflexive transitive closure of the supported direct corridors. -/
inductive Reach : Artifact → Artifact → Prop where
  | refl (a : Artifact) : Reach a a
  | edge {a b : Artifact} (h : EvidenceEdge a b) : Reach a b
  | trans {a b c : Artifact} (hab : Reach a b) (hbc : Reach b c) : Reach a c

theorem height_le_of_reach {a b : Artifact} (h : Reach a b) :
    height a ≤ height b := by
  induction h with
  | refl _ => exact le_rfl
  | edge h => exact (height_lt_of_edge h).le
  | trans _ _ ih₁ ih₂ => exact le_trans ih₁ ih₂

instance instLEArtifact : LE Artifact := ⟨Reach⟩

/-- Reachability along the selected directed bridges forms a partial order;
branches without bridge evidence remain incomparable. -/
instance instPartialOrderArtifact : PartialOrder Artifact where
  le_refl := Reach.refl
  le_trans := by
    intro a b c hab hbc
    exact Reach.trans hab hbc
  le_antisymm := by
    intro a b hab hba
    apply height_injective
    exact Nat.le_antisymm (height_le_of_reach hab) (height_le_of_reach hba)

theorem universalCell_precedes_matrixUnit :
    Artifact.universalCl11Cell ≤ Artifact.cl11MatrixUnit :=
  Reach.edge (.universalCell_to_matrixUnit cl11MatrixAlgEquiv_abstractNullPlus)

theorem universalCell_precedes_peirceProjector :
    Artifact.universalCl11Cell ≤ Artifact.cl11PeirceProjector :=
  Reach.edge (.universalCell_to_peirce abstractVacProj_idempotent)

theorem matrixUnit_precedes_wittBase :
    Artifact.cl11MatrixUnit ≤ Artifact.wittCreationBase :=
  Reach.edge (.matrixUnit_to_wittBase matrixUnit_eq_wittCreationBase)

theorem wittBase_precedes_finiteJordanWigner :
    Artifact.wittCreationBase ≤ Artifact.finiteJordanWigner :=
  Reach.edge (.wittBase_to_finiteJW jwCreation_eq_base_string)

theorem finiteJordanWigner_precedes_colimitJordanWigner :
    Artifact.finiteJordanWigner ≤ Artifact.colimitJordanWigner :=
  Reach.edge (.finiteJW_to_colimitJW colimitJWCreation_eq_stageInjection)

theorem colimitJordanWigner_precedes_mixedCAR :
    Artifact.colimitJordanWigner ≤ Artifact.colimitMixedCAR :=
  Reach.edge (.colimitJW_to_mixedCAR colimitJW_annihilation_creation_anticomm_all)

theorem paraProjectors_precede_mobiusQuotient :
    Artifact.paraProjectorLaws ≤ Artifact.mobiusSetQuotient :=
  Reach.edge (.paraProjectors_to_mobiusQuotient
    (by
      intro V _ _ K C hC v
      exact paraProjectorQuotientCorridor hC v))

theorem mobiusQuotient_precedes_crossSheetPairingDescent :
    Artifact.mobiusSetQuotient ≤ Artifact.mobiusCrossSheetPairingDescent :=
  Reach.edge (.mobiusQuotient_to_crossSheetPairing
    (by
      intro V _ _ g omega K C hK hPK hC hC_iso q
      exact mobiusQuotientQuadratic_eq_two_mul_crossSheetPairing
        g omega hK hPK hC hC_iso q))

theorem flowAndBoundary_precede_crossStageKMS :
    Artifact.flowAndKMSBoundaryLemmas ≤ Artifact.crossStageKMSReadout := by
  apply Reach.edge
  refine .flowAndBoundary_to_crossStageReadout ?_
  intro k n hle logits β t A B ⟨hFlow, hKMS⟩
  rw [hFlow]
  exact hKMS

theorem prunedFacts_imply_crossStageSinkBound
    {k n : ℕ} (hle : k ≤ n) (pw : PrunedWeights (Fin (2 ^ k)))
    (logits : Fin (2 ^ k) → ℝ) (β t : ℝ) (anchor : Fin (2 ^ k))
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    (selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection k
          (modularFlow logits β t (complexifyRealMatrix (A.transpose * A)))) =
      selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection k (complexifyRealMatrix (A.transpose * A)))) →
    (pw.weights anchor * (∑ j : Fin (2 ^ k), (A j anchor) ^ 2) ≤
      (selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection k (complexifyRealMatrix (A.transpose * A)))).re) →
    pw.weights anchor * (∑ j : Fin (2 ^ k), (A j anchor) ^ 2) ≤
      (selectedStageColimitFunctional k (prunedStageDensity k pw)
        (stageInjection n
          (rawMap hle
            (modularFlow logits β t
              (complexifyRealMatrix (A.transpose * A)))))).re := by
  intro hFlow hAnchor
  rw [stageInjection_transition hle, hFlow]
  exact hAnchor

theorem prunedFacts_precede_crossStageSinkBound :
    Artifact.prunedStageReadoutAndAnchorBound ≤ Artifact.prunedCrossStageSinkBound :=
  Reach.edge (.prunedFacts_to_crossStageSinkBound (by
    intro k n hle pw logits β t anchor A ⟨hFlow, hAnchor⟩
    exact prunedFacts_imply_crossStageSinkBound
      hle pw logits β t anchor A hFlow hAnchor))

/-!
## Multi-Step Transitive Corridor Chains (`≤` and strict `<`)
-/

theorem universalCell_precedes_wittBase :
    Artifact.universalCl11Cell ≤ Artifact.wittCreationBase :=
  le_trans universalCell_precedes_matrixUnit matrixUnit_precedes_wittBase

theorem universalCell_precedes_finiteJordanWigner :
    Artifact.universalCl11Cell ≤ Artifact.finiteJordanWigner :=
  le_trans universalCell_precedes_wittBase wittBase_precedes_finiteJordanWigner

theorem universalCell_precedes_colimitJordanWigner :
    Artifact.universalCl11Cell ≤ Artifact.colimitJordanWigner :=
  le_trans universalCell_precedes_finiteJordanWigner finiteJordanWigner_precedes_colimitJordanWigner

theorem universalCell_precedes_colimitMixedCAR :
    Artifact.universalCl11Cell ≤ Artifact.colimitMixedCAR :=
  le_trans universalCell_precedes_colimitJordanWigner colimitJordanWigner_precedes_mixedCAR

theorem universalCell_lt_colimitJordanWigner :
    Artifact.universalCl11Cell < Artifact.colimitJordanWigner :=
  lt_of_le_of_ne universalCell_precedes_colimitJordanWigner (by decide)

theorem universalCell_lt_colimitMixedCAR :
    Artifact.universalCl11Cell < Artifact.colimitMixedCAR :=
  lt_of_le_of_ne universalCell_precedes_colimitMixedCAR (by decide)

theorem paraProjectors_precede_crossSheetPairingDescent :
    Artifact.paraProjectorLaws ≤ Artifact.mobiusCrossSheetPairingDescent :=
  le_trans paraProjectors_precede_mobiusQuotient mobiusQuotient_precedes_crossSheetPairingDescent

theorem paraProjectors_lt_mobiusQuotient :
    Artifact.paraProjectorLaws < Artifact.mobiusSetQuotient :=
  lt_of_le_of_ne paraProjectors_precede_mobiusQuotient (by decide)

theorem paraProjectors_lt_crossSheetPairingDescent :
    Artifact.paraProjectorLaws < Artifact.mobiusCrossSheetPairingDescent :=
  lt_of_le_of_ne paraProjectors_precede_crossSheetPairingDescent (by decide)

theorem flowAndBoundary_lt_crossStageKMS :
    Artifact.flowAndKMSBoundaryLemmas < Artifact.crossStageKMSReadout :=
  lt_of_le_of_ne flowAndBoundary_precede_crossStageKMS (by decide)

theorem prunedFacts_lt_crossStageSinkBound :
    Artifact.prunedStageReadoutAndAnchorBound < Artifact.prunedCrossStageSinkBound :=
  lt_of_le_of_ne prunedFacts_precede_crossStageSinkBound (by decide)

/-!
## Explicit Structural Separation, Isolation & Incomparability Theorems
-/

/-- If an artifact `a` has no outgoing `EvidenceEdge`, then `Reach a b` forces `b = a`. -/
theorem reach_eq_of_no_outgoing {a b : Artifact} (h : Reach a b) :
    (∀ c : Artifact, ¬ EvidenceEdge a c) → b = a := by
  induction h with
  | refl _ =>
    intro _
    rfl
  | edge he =>
    intro hno
    exact False.elim (hno _ he)
  | trans _ _ ih₁ ih₂ =>
    intro hno
    have hba := ih₁ hno
    subst hba
    exact ih₂ hno

/-- If an artifact `b` has no incoming `EvidenceEdge`, then `Reach a b` forces `a = b`. -/
theorem reach_eq_of_no_incoming {a b : Artifact} (h : Reach a b) :
    (∀ c : Artifact, ¬ EvidenceEdge c b) → a = b := by
  induction h with
  | refl _ =>
    intro _
    rfl
  | edge he =>
    intro hno
    exact False.elim (hno _ he)
  | trans _ _ ih₁ ih₂ =>
    intro hno
    have hbc := ih₂ hno
    subst hbc
    exact ih₁ hno

theorem no_edge_from_fisherClassification (b : Artifact) :
    ¬ EvidenceEdge .fisherClassification b := by
  intro h
  cases h

theorem no_edge_to_fisherClassification (a : Artifact) :
    ¬ EvidenceEdge a .fisherClassification := by
  intro h
  cases h

theorem reach_from_fisherClassification_eq {b : Artifact}
    (h : Artifact.fisherClassification ≤ b) :
    b = .fisherClassification :=
  reach_eq_of_no_outgoing h no_edge_from_fisherClassification

theorem reach_to_fisherClassification_eq {a : Artifact}
    (h : a ≤ Artifact.fisherClassification) :
    a = .fisherClassification :=
  reach_eq_of_no_incoming h no_edge_to_fisherClassification

theorem no_edge_from_paraKahlerNullSheets (b : Artifact) :
    ¬ EvidenceEdge .paraKahlerNullSheets b := by
  intro h
  cases h

theorem no_edge_to_paraKahlerNullSheets (a : Artifact) :
    ¬ EvidenceEdge a .paraKahlerNullSheets := by
  intro h
  cases h

theorem reach_from_paraKahlerNullSheets_eq {b : Artifact}
    (h : Artifact.paraKahlerNullSheets ≤ b) :
    b = .paraKahlerNullSheets :=
  reach_eq_of_no_outgoing h no_edge_from_paraKahlerNullSheets

theorem reach_to_paraKahlerNullSheets_eq {a : Artifact}
    (h : a ≤ Artifact.paraKahlerNullSheets) :
    a = .paraKahlerNullSheets :=
  reach_eq_of_no_incoming h no_edge_to_paraKahlerNullSheets

theorem no_edge_from_mobiusCrossSheetPairingDescent (b : Artifact) :
    ¬ EvidenceEdge .mobiusCrossSheetPairingDescent b := by
  intro h
  cases h

theorem reach_from_mobiusCrossSheetPairingDescent_eq {b : Artifact}
    (h : Artifact.mobiusCrossSheetPairingDescent ≤ b) :
    b = .mobiusCrossSheetPairingDescent :=
  reach_eq_of_no_outgoing h no_edge_from_mobiusCrossSheetPairingDescent

theorem edge_from_mobiusSetQuotient_eq {b : Artifact}
    (h : EvidenceEdge .mobiusSetQuotient b) :
    b = .mobiusCrossSheetPairingDescent := by
  cases h
  rfl

theorem reach_from_mobiusSetQuotient_aux {a b : Artifact} (h : Reach a b) :
    a = .mobiusSetQuotient →
      b = .mobiusSetQuotient ∨ b = .mobiusCrossSheetPairingDescent := by
  induction h with
  | refl _ =>
    intro ha
    exact Or.inl ha
  | edge he =>
    intro ha
    subst ha
    exact Or.inr (edge_from_mobiusSetQuotient_eq he)
  | trans _ hbc ih₁ ih₂ =>
    intro ha
    rcases ih₁ ha with hmid | hmid
    · exact ih₂ hmid
    · subst hmid
      exact Or.inr (reach_from_mobiusCrossSheetPairingDescent_eq hbc)

theorem reach_from_mobiusSetQuotient_eq_or {b : Artifact}
    (h : Artifact.mobiusSetQuotient ≤ b) :
    b = .mobiusSetQuotient ∨ b = .mobiusCrossSheetPairingDescent :=
  reach_from_mobiusSetQuotient_aux h rfl

theorem fisherClassification_incomparable_universalCell :
    ¬ (Artifact.fisherClassification ≤ .universalCl11Cell) ∧
      ¬ (Artifact.universalCl11Cell ≤ .fisherClassification) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact Artifact.noConfusion (reach_from_fisherClassification_eq h)
  · intro h
    exact Artifact.noConfusion (reach_to_fisherClassification_eq h)

theorem paraKahlerNullSheets_incomparable_paraProjectorLaws :
    ¬ (Artifact.paraKahlerNullSheets ≤ .paraProjectorLaws) ∧
      ¬ (Artifact.paraProjectorLaws ≤ .paraKahlerNullSheets) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact Artifact.noConfusion (reach_from_paraKahlerNullSheets_eq h)
  · intro h
    exact Artifact.noConfusion (reach_to_paraKahlerNullSheets_eq h)

theorem mobiusSetQuotient_incomparable_crossStageKMSReadout :
    ¬ (Artifact.mobiusSetQuotient ≤ .crossStageKMSReadout) ∧
      ¬ (Artifact.crossStageKMSReadout ≤ .mobiusSetQuotient) := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases reach_from_mobiusSetQuotient_eq_or h with h₁ | h₂
    · exact Artifact.noConfusion h₁
    · exact Artifact.noConfusion h₂
  · intro h
    have hle := height_le_of_reach h
    revert hle
    decide

theorem colimitJordanWigner_incomparable_mobiusSetQuotient :
    ¬ (Artifact.colimitJordanWigner ≤ .mobiusSetQuotient) ∧
      ¬ (Artifact.mobiusSetQuotient ≤ .colimitJordanWigner) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hle := height_le_of_reach h
    revert hle
    decide
  · intro h
    rcases reach_from_mobiusSetQuotient_eq_or h with h₁ | h₂
    · exact Artifact.noConfusion h₁
    · exact Artifact.noConfusion h₂

theorem mobiusCrossSheetPairingDescent_incomparable_crossStageKMSReadout :
    ¬ (Artifact.mobiusCrossSheetPairingDescent ≤ .crossStageKMSReadout) ∧
      ¬ (Artifact.crossStageKMSReadout ≤ .mobiusCrossSheetPairingDescent) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact Artifact.noConfusion (reach_from_mobiusCrossSheetPairingDescent_eq h)
  · intro h
    have no_out : ∀ c : Artifact, ¬ EvidenceEdge .crossStageKMSReadout c := by
      intro c hc
      cases hc
    exact Artifact.noConfusion (reach_eq_of_no_outgoing h no_out)

/-!
## Native Mathlib `ReflTransGen`, `TransGen`, `OrderHom`, `StrictMono`, and Non-Totality (`¬ IsTotal`)
-/

/-- Every `Reach a b` derivation induces `Relation.ReflTransGen EvidenceEdge a b`. -/
theorem reach_to_reflTransGen {a b : Artifact} (h : Reach a b) :
    Relation.ReflTransGen EvidenceEdge a b := by
  induction h with
  | refl _ => exact Relation.ReflTransGen.refl
  | edge he => exact Relation.ReflTransGen.single he
  | trans _ _ ih₁ ih₂ => exact Relation.ReflTransGen.trans ih₁ ih₂

/-- Every `Relation.ReflTransGen EvidenceEdge a b` derivation induces `Reach a b`. -/
theorem reflTransGen_to_reach {a b : Artifact}
    (h : Relation.ReflTransGen EvidenceEdge a b) : Reach a b := by
  induction h with
  | refl => exact Reach.refl a
  | tail _ hbc ih => exact Reach.trans ih (Reach.edge hbc)

/-- Equivalence of the partial-order relation `a ≤ b` on `Artifact` with Mathlib's reflexive
transitive closure `Relation.ReflTransGen EvidenceEdge a b`. -/
theorem le_iff_reflTransGen_evidenceEdge (a b : Artifact) :
    a ≤ b ↔ Relation.ReflTransGen EvidenceEdge a b :=
  ⟨reach_to_reflTransGen, reflTransGen_to_reach⟩

/-- `height` packaged as an order-preserving homomorphism `Artifact →o ℕ`. -/
def heightOrderHom : Artifact →o ℕ where
  toFun := height
  monotone' _ _ h := height_le_of_reach h

@[simp]
theorem heightOrderHom_apply (a : Artifact) :
    heightOrderHom a = height a :=
  rfl

/-- `height` is strictly monotone with respect to the strict partial order `<` on `Artifact`. -/
theorem height_strictMono : StrictMono height := by
  intro a b hab
  exact lt_of_le_of_ne (height_le_of_reach (le_of_lt hab))
    (fun heq => ne_of_lt hab (height_injective heq))

/-- Every non-empty directed path `Relation.TransGen EvidenceEdge a b` induces strict
precedence `a < b` in the `Artifact` partial order. -/
theorem transGen_to_lt {a b : Artifact}
    (h : Relation.TransGen EvidenceEdge a b) : a < b := by
  induction h with
  | single he =>
    exact lt_of_le_of_ne (Reach.edge he)
      (fun hab => Nat.ne_of_lt (height_lt_of_edge he) (congrArg height hab))
  | tail _ he ih =>
    exact lt_of_lt_of_le ih (Reach.edge he)

/-- Every `Reach a b` derivation is either reflexive (`a = b`) or a non-empty directed path
(`Relation.TransGen EvidenceEdge a b`). -/
theorem reach_eq_or_transGen {a b : Artifact} (h : Reach a b) :
    a = b ∨ Relation.TransGen EvidenceEdge a b := by
  induction h with
  | refl _ => exact Or.inl rfl
  | edge he => exact Or.inr (Relation.TransGen.single he)
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | h₁
    · exact ih₂
    · rcases ih₂ with rfl | h₂
      · exact Or.inr h₁
      · exact Or.inr (Relation.TransGen.trans h₁ h₂)

/-- Equivalence of strict precedence `a < b` on `Artifact` with Mathlib's transitive closure
`Relation.TransGen EvidenceEdge a b`. -/
theorem lt_iff_transGen_evidenceEdge (a b : Artifact) :
    a < b ↔ Relation.TransGen EvidenceEdge a b := by
  constructor
  · intro hab
    rcases reach_eq_or_transGen (le_of_lt hab) with h_eq | h_trans
    · exact False.elim (ne_of_lt hab h_eq)
    · exact h_trans
  · exact transGen_to_lt

/-- The partial order `(Artifact, ≤)` is not a total (linear) order: independent synthesis
corridors remain strictly incomparable. -/
theorem not_total_artifact_le : ¬ Std.Total (α := Artifact) (· ≤ ·) := by
  intro htot
  rcases htot.total Artifact.fisherClassification Artifact.universalCl11Cell with h₁ | h₂
  · exact fisherClassification_incomparable_universalCell.1 h₁
  · exact fisherClassification_incomparable_universalCell.2 h₂

/-- Explicit non-totality of `(Artifact, ≤)`: it is false that every pair of synthesis artifacts is
comparable. -/
theorem not_forall_le_or_le_artifact : ¬ ∀ a b : Artifact, a ≤ b ∨ b ≤ a := by
  intro hall
  rcases hall Artifact.fisherClassification Artifact.universalCl11Cell with h₁ | h₂
  · exact fisherClassification_incomparable_universalCell.1 h₁
  · exact fisherClassification_incomparable_universalCell.2 h₂

end InfoGeometry.Synthesis.CategoricalInevitabilityCausalPoset

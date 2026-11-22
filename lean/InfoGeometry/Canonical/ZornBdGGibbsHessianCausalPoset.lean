/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Order
import InfoGeometry.Canonical.ZornBdGGibbsHessianBridge

/-!
# Causal poset for the Zorn--BdG--Gibbs Hessian theorem corridor

The order is the inclusion order on prerequisite sets for the source-backed
stages of `ZornBdGGibbsHessianBridge`.  It records proof dependencies, not
physical causation.  In particular, the pairing-direction and Gibbs-state
branches remain distinct until the log-partition Hessian theorem consumes both.
The positive-partition stage is an explicit hypothesis, not a newly proved
positivity theorem.
-/

namespace InfoGeometry.Canonical.ZornBdGGibbsHessianCausalPoset

/-- Proof stages for the actual finite operator/Zorn/Gibbs theorem chain. -/
inductive Stage where
  | operatorCarrier
  | zornReadout
  | bdgCompatibility
  | selfAdjointBdGOperator
  | pairingSectorDirection
  | selfAdjointPairingDirection
  | positivePartition
  | faithfulGibbsModularData
  | centeredBKMCovariance
  | logPartitionHessian
  | nonnegativePairingResponse
  deriving DecidableEq, Repr

/-- Prerequisite-index encoding of the theorem dependencies.  The two sets
`bdgCompatibility` and `pairingSectorDirection` are incomparable; their
requirements meet when self-adjointness of the pairing direction is proved. -/
def prerequisites : Stage → Finset ℕ
  | .operatorCarrier => {0}
  | .zornReadout => {0, 1}
  | .bdgCompatibility => {0, 1, 2}
  | .selfAdjointBdGOperator => {0, 1, 2, 3}
  | .pairingSectorDirection => {0, 1, 4}
  | .selfAdjointPairingDirection => {0, 1, 2, 3, 4, 5}
  | .positivePartition => {0, 1, 2, 3, 6}
  | .faithfulGibbsModularData => {0, 1, 2, 3, 6, 7}
  | .centeredBKMCovariance => {0, 1, 2, 3, 6, 7, 8}
  | .logPartitionHessian => {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
  | .nonnegativePairingResponse => {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}

theorem prerequisites_injective : Function.Injective prerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

/-- The source prerequisite inclusion gives a genuine partial order. -/
instance : PartialOrder Stage := PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Stage) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

/-- The common finite operator carrier precedes every encoded stage. -/
theorem operatorCarrier_precedes_all (s : Stage) : Stage.operatorCarrier ≤ s := by
  cases s <;> decide

/-- The Zorn block readout is used by the compatibility and self-adjointness
results in the bridge module. -/
theorem zornReadout_precedes_compatibility :
    Stage.zornReadout ≤ Stage.bdgCompatibility := by decide

theorem compatibility_precedes_selfAdjointBdG :
    Stage.bdgCompatibility ≤ Stage.selfAdjointBdGOperator := by decide

/-- Extracting the pairing-sector operator is a separate branch from proving
that arbitrary BdG readouts satisfy the adjoint-block convention. -/
theorem pairing_and_compatibility_incomparable :
    ¬ Stage.pairingSectorDirection ≤ Stage.bdgCompatibility ∧
      ¬ Stage.bdgCompatibility ≤ Stage.pairingSectorDirection := by decide

theorem pairing_and_compatibility_precede_selfAdjoint_direction :
    Stage.pairingSectorDirection ≤ Stage.selfAdjointPairingDirection ∧
      Stage.bdgCompatibility ≤ Stage.selfAdjointPairingDirection := by decide

/-- The positive-partition assumption and self-adjoint BdG construction feed
the faithful Gibbs modular data used by the BKM covariance. -/
theorem Gibbs_hypotheses_precede_faithful_modular_data :
    Stage.selfAdjointBdGOperator ≤ Stage.faithfulGibbsModularData ∧
      Stage.positivePartition ≤ Stage.faithfulGibbsModularData := by decide

theorem modular_data_precedes_centered_BKM :
    Stage.faithfulGibbsModularData ≤ Stage.centeredBKMCovariance := by decide

/-- The Hessian stage joins the pairing-direction branch with the faithful
Gibbs/BKM branch; positivity is the final diagonal consequence. -/
theorem Hessian_joins_pairing_and_BKM :
    Stage.selfAdjointPairingDirection ≤ Stage.logPartitionHessian ∧
      Stage.centeredBKMCovariance ≤ Stage.logPartitionHessian := by decide

theorem Hessian_precedes_nonnegative_response :
    Stage.logPartitionHessian ≤ Stage.nonnegativePairingResponse := by decide

end InfoGeometry.Canonical.ZornBdGGibbsHessianCausalPoset

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Dependency partial order of the Peirce-coupling compilation

This finite order specifies mathematical stages, not an extracted declaration
graph or physical causality. The Gram stage includes faithful trace and kernel
results as well as positivity; trace and adjoint inputs remain incomparable.
-/

namespace InfoGeometry.NCG.OppositePeirceOrder

inductive Stage where
  | corners | grading | coupling | trace | adjoint | gram | krein | witness
  deriving DecidableEq

instance : Fintype Stage where
  elems := {Stage.corners, Stage.grading, Stage.coupling, Stage.trace,
    Stage.adjoint, Stage.gram, Stage.krein, Stage.witness}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .corners => {Stage.corners}
  | .grading => {Stage.corners, Stage.grading}
  | .coupling => {Stage.corners, Stage.grading, Stage.coupling}
  | .trace => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace}
  | .adjoint => {Stage.corners, Stage.adjoint}
  | .gram => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace, Stage.adjoint, Stage.gram}
  | .krein => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace,
      Stage.adjoint, Stage.gram, Stage.krein}
  | .witness => {Stage.corners, Stage.grading, Stage.coupling, Stage.trace,
      Stage.adjoint, Stage.gram, Stage.krein, Stage.witness}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem trace_adjoint_incomparable :
    ¬Stage.trace ≤ Stage.adjoint ∧ ¬Stage.adjoint ≤ Stage.trace := by decide

theorem metric_stage_requires_both : Stage.trace ≤ Stage.gram ∧ Stage.adjoint ≤ Stage.gram := by
  decide

theorem stages_reach_witness (s : Stage) : s ≤ Stage.witness := by cases s <;> decide

end InfoGeometry.NCG.OppositePeirceOrder

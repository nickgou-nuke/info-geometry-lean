/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# A finite partial order for the graded inverse compilation stages

This is an explicit dependency specification, not a claim to extract Lean's
entire declaration graph. In particular the metric and algebraic inverse
branches remain incomparable before their joint recovery stage.
-/

namespace InfoGeometry.Canonical.GradedDMPDependencyOrder

inductive Stage where
  | retract | peirce | drazin | penrose | hybrid | obstruction | transport | witness
  deriving DecidableEq

instance : Fintype Stage where
  elems := {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose,
    Stage.hybrid, Stage.obstruction, Stage.transport, Stage.witness}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .retract => {Stage.retract}
  | .peirce => {Stage.retract, Stage.peirce}
  | .drazin => {Stage.retract, Stage.peirce, Stage.drazin}
  | .penrose => {Stage.penrose}
  | .hybrid => {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose, Stage.hybrid}
  | .obstruction =>
      {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose, Stage.hybrid, Stage.obstruction}
  | .transport =>
      {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose, Stage.hybrid, Stage.transport}
  | .witness => {Stage.retract, Stage.peirce, Stage.drazin, Stage.penrose,
      Stage.hybrid, Stage.obstruction, Stage.transport, Stage.witness}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem inverse_branches_incomparable :
    ¬Stage.drazin ≤ Stage.penrose ∧ ¬Stage.penrose ≤ Stage.drazin := by decide

theorem join_requires_both : Stage.drazin ≤ Stage.hybrid ∧ Stage.penrose ≤ Stage.hybrid := by
  decide

theorem continuation_branches_incomparable :
    ¬Stage.obstruction ≤ Stage.transport ∧ ¬Stage.transport ≤ Stage.obstruction := by decide

theorem stages_reach_witness (s : Stage) : s ≤ Stage.witness := by cases s <;> decide

end InfoGeometry.Canonical.GradedDMPDependencyOrder

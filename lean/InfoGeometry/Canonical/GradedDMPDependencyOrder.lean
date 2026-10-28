/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# A finite partial order for the graded inverse compilation stages

This is an explicit dependency specification, not a claim to extract Lean's
entire declaration graph. In particular the metric and algebraic inverse
branches remain incomparable before their joint recovery stage.
-/

namespace InfoGeometry.Canonical.GradedDMPDependencyOrder

inductive Stage where
  | retract | peirce | drazin | penrose | hybrid | obstruction | transport | witness
  deriving DecidableEq, Fintype

open Stage

def prerequisites : Stage → Finset Stage
  | retract => {retract}
  | peirce => {retract, peirce}
  | drazin => {retract, peirce, drazin}
  | penrose => {penrose}
  | hybrid => {retract, peirce, drazin, penrose, hybrid}
  | obstruction => {retract, peirce, drazin, penrose, hybrid, obstruction}
  | transport => {retract, peirce, drazin, penrose, hybrid, transport}
  | witness => {retract, peirce, drazin, penrose, hybrid, obstruction, transport, witness}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem inverse_branches_incomparable : ¬drazin ≤ penrose ∧ ¬penrose ≤ drazin := by decide

theorem join_requires_both : drazin ≤ hybrid ∧ penrose ≤ hybrid := by decide

theorem continuation_branches_incomparable :
    ¬obstruction ≤ transport ∧ ¬transport ≤ obstruction := by decide

theorem stages_reach_witness (s : Stage) : s ≤ witness := by cases s <;> decide

end InfoGeometry.Canonical.GradedDMPDependencyOrder

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-! # A finite prerequisite order for the two source streams

The relation records sufficient mathematical prerequisites, not physical
causation or an extracted whole-repository declaration graph.
-/
namespace InfoGeometry.Core.PeirceSourceOrder

inductive Stage
  | algebra | support | octet | frame | trace | reflection | iteration | synthesis
  deriving DecidableEq

open Stage

instance : Fintype Stage where
  elems := {algebra, support, octet, frame, trace, reflection, iteration, synthesis}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | algebra => {algebra}
  | support => {algebra, support}
  | octet => {algebra, octet}
  | frame => {algebra, support, frame}
  | trace => {algebra, octet, trace}
  | reflection => {algebra, support,octet, reflection}
  | iteration => {algebra, support, frame, iteration}
  | synthesis => Finset.univ

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem support_octet_independent : ¬ support ≤ octet ∧ ¬ octet ≤ support := by decide

theorem trace_frame_independent : ¬ trace ≤ frame ∧ ¬ frame ≤ trace := by decide

theorem frame_precedes_iteration : frame ≤ iteration := by decide

theorem reflection_joins_inputs : support ≤ reflection ∧ octet ≤ reflection := by decide

theorem synthesis_covers (s : Stage) : s ≤ synthesis := by cases s <;> decide

end InfoGeometry.Core.PeirceSourceOrder

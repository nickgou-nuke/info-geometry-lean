/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-! # Prerequisite poset for the signed-transport compilation

This is a sufficient mathematical stage order, not an extracted declaration
DAG or physical causality. Peirce support and metric input are independent;
cyclic trace identities do not imply positivity. Generic octet identities do
not need a Peirce projector or square-zero generators.
-/

namespace InfoGeometry.OperatorAlgebra.SignedTransportOrder

inductive Stage
  | algebra | octet | corners | nilpotent | routing | trace | metric | synthesis
  deriving DecidableEq

open Stage

instance : Fintype Stage where
  elems := {algebra, octet, corners, nilpotent, routing, trace, metric, synthesis}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .algebra => {algebra}
  | .octet => {algebra, octet}
  | .corners => {algebra, corners}
  | .nilpotent => {algebra, nilpotent}
  | .routing => {algebra, corners, routing}
  | .trace => {algebra, trace}
  | .metric => {algebra, metric}
  | .synthesis => Finset.univ

theorem prerequisites_injective : Function.Injective prerequisites := by
  intro a b h
  have ha : a ∈ prerequisites b := by
    rw [← h]
    cases a <;> simp [prerequisites]
  have hb : b ∈ prerequisites a := by
    rw [h]
    cases b <;> simp [prerequisites]
  clear h
  cases a <;> cases b <;> simp_all [prerequisites]

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem octet_corners_independent : ¬ octet ≤ corners ∧ ¬ corners ≤ octet := by
  change ¬ prerequisites octet ⊆ prerequisites corners ∧
    ¬ prerequisites corners ⊆ prerequisites octet
  simp [prerequisites, Finset.subset_iff]

theorem routing_metric_independent : ¬ routing ≤ metric ∧ ¬ metric ≤ routing := by
  change ¬ prerequisites routing ⊆ prerequisites metric ∧
    ¬ prerequisites metric ⊆ prerequisites routing
  simp [prerequisites, Finset.subset_iff]

theorem trace_metric_independent : ¬ trace ≤ metric ∧ ¬ metric ≤ trace := by
  change ¬ prerequisites trace ⊆ prerequisites metric ∧
    ¬ prerequisites metric ⊆ prerequisites trace
  simp [prerequisites, Finset.subset_iff]

theorem synthesis_contains_all (s : Stage) : s ≤ synthesis := by
  change prerequisites s ⊆ Finset.univ
  exact Finset.subset_univ _

end InfoGeometry.OperatorAlgebra.SignedTransportOrder

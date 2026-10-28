/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-! # Explicit dependency order of the boundary compilation

This finite partial order specifies sufficient theorem stages, not an extracted
Lean declaration graph or physical time. Nilpotence makes a differential complex;
the metric adjoint supplies positive energy. Those are separate prerequisites
for the combined complex-with-adjoint stage, although the energy formula alone
does not require nilpotence.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder

inductive Stage
  | associative | lieJordan | peirce | compositions | differential | adjoint | hodge | tests
  deriving DecidableEq

open Stage

instance : Fintype Stage where
  elems := {associative, lieJordan, Stage.peirce, compositions, differential,
    adjoint, hodge, tests}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .associative => {associative}
  | .lieJordan => {associative, lieJordan}
  | .peirce => {associative, Stage.peirce}
  | .compositions => {associative, lieJordan, compositions}
  | .differential => {associative, lieJordan, Stage.peirce, differential}
  | .adjoint => {associative, lieJordan, Stage.peirce, adjoint}
  | .hodge => {associative, lieJordan, Stage.peirce, differential, adjoint, hodge}
  | .tests => Finset.univ

theorem prerequisites_injective : Function.Injective prerequisites := by
  intro a b h
  have ha : a ∈ prerequisites b := by
    rw [← h]
    cases a <;> simp [prerequisites]
  have hb : b ∈ prerequisites a := by
    rw [h]
    cases b <;> simp [prerequisites]
  cases a <;> cases b <;> simp_all [prerequisites]

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem boundary_metric_incomparable :
    ¬ differential ≤ adjoint ∧ ¬ adjoint ≤ differential := by
  change ¬ prerequisites differential ⊆ prerequisites adjoint ∧
    ¬ prerequisites adjoint ⊆ prerequisites differential
  simp [prerequisites, Finset.subset_iff]

theorem hodge_requires_both : differential ≤ hodge ∧ adjoint ≤ hodge := by
  change prerequisites differential ⊆ prerequisites hodge ∧
    prerequisites adjoint ⊆ prerequisites hodge
  simp [prerequisites, Finset.subset_iff]

theorem mixed_and_boundary_incomparable :
    ¬ compositions ≤ differential ∧ ¬ differential ≤ compositions := by
  change ¬ prerequisites compositions ⊆ prerequisites differential ∧
    ¬ prerequisites differential ⊆ prerequisites compositions
  simp [prerequisites, Finset.subset_iff]

theorem witnesses_cover_all (s : Stage) : s ≤ tests := by
  change prerequisites s ⊆ Finset.univ
  exact Finset.subset_univ _

end InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder

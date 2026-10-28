/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-! # Explicit dependency order of the boundary compilation

This finite partial order specifies theorem stages. It is not an extracted
Lean declaration graph or a physical time order. In particular the algebraic
boundary and metric-adjoint inputs are independent prerequisites of Hodge energy.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder

inductive Stage
  | associative | lieJordan | peirce | compositions | differential | adjoint | hodge | tests
  deriving DecidableEq

open Stage

instance : Fintype Stage where
  elems := {associative, lieJordan, peirce, compositions, differential, adjoint, hodge, tests}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | associative => {associative}
  | lieJordan => {associative, lieJordan}
  | peirce => {associative, peirce}
  | compositions => {associative, lieJordan, compositions}
  | differential => {associative, lieJordan, peirce, differential}
  | adjoint => {associative, lieJordan, peirce, adjoint}
  | hodge => {associative, lieJordan, peirce, differential, adjoint, hodge}
  | tests => Finset.univ

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem boundary_metric_incomparable :
    ¬ differential ≤ adjoint ∧ ¬ adjoint ≤ differential := by decide

theorem hodge_requires_both : differential ≤ hodge ∧ adjoint ≤ hodge := by decide

theorem mixed_and_boundary_incomparable :
    ¬ compositions ≤ differential ∧ ¬ differential ≤ compositions := by decide

theorem witnesses_cover_all (s : Stage) : s ≤ tests := by cases s <;> decide

end InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder

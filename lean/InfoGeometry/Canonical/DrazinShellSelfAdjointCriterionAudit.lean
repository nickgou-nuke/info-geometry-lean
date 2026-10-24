/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinShellSelfAdjointCriterion
import InfoGeometry.Canonical.DrazinShellConsequenceExamples
open InfoGeometry.Canonical.DrazinShellSelfAdjointCriterion
open InfoGeometry.Canonical.DrazinNilpotentShell
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.ObliqueShellCounterexample
open InfoGeometry.Canonical.DrazinShellConsequenceExamples

#print axioms finite_shells_selfAdjoint_iff
#print axioms all_shells_selfAdjoint_iff
#print axioms exists_nonselfAdjoint_shell_iff
#print axioms oblique_shell_zero_not_selfadjoint

example : ¬ IsSelfAdjoint (complementaryProjection obliqueA obliqueD) := by
  intro h
  exact oblique_shell_zero_not_selfadjoint
    ((all_shells_selfAdjoint_iff oblique_drazin oblique_mp_family).mpr h 0)

example : ∃ m ∈ Finset.range 2,
    ¬ IsSelfAdjoint (drazinShellProj obliqueA obliqueD obliquePowers m) := by
  exact ⟨0, by decide, oblique_shell_zero_not_selfadjoint⟩

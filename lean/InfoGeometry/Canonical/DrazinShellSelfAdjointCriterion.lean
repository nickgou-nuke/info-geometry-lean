/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinNilpotentShellResolution

/-! Exact self-adjointness criterion for the entire native dressed shell
resolution. No minimal-index or nonzero-shell hypothesis is needed. -/
namespace InfoGeometry.Canonical.DrazinShellSelfAdjointCriterion
open Drazin Drazin.IsDrazinInverse DrazinNilpotentShell MoorePenrose
variable {R : Type*} [Ring R] [StarRing R]
variable {a d : R} {k : ℕ} {M : ℕ → R}

theorem finite_shells_selfAdjoint_iff (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    (∀ m ∈ Finset.range k, IsSelfAdjoint (drazinShellProj a d M m)) ↔
      IsSelfAdjoint (complementaryProjection a d) := by
  constructor
  · intro hS
    change star (complementaryProjection a d) = complementaryProjection a d
    rw [← sum_drazinShellProj_eq_complementaryProjection hD hM, star_sum]
    exact Finset.sum_congr rfl (fun m hm => hS m hm)
  · intro hS m _
    exact drazinShellProj_selfAdjoint hD hM hS m

theorem all_shells_selfAdjoint_iff (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    (∀ m, IsSelfAdjoint (drazinShellProj a d M m)) ↔
      IsSelfAdjoint (complementaryProjection a d) := by
  constructor
  · intro hS
    exact (finite_shells_selfAdjoint_iff hD hM).mp (fun m _ => hS m)
  · intro hS m
    exact drazinShellProj_selfAdjoint hD hM hS m

theorem exists_nonselfAdjoint_shell_iff (hD : IsDrazinInverse a d k)
    (hM : PowerMPFamily (fittingNilpotentPart a d) M) :
    (∃ m ∈ Finset.range k, ¬ IsSelfAdjoint (drazinShellProj a d M m)) ↔
      ¬ IsSelfAdjoint (complementaryProjection a d) := by
  classical
  simpa only [not_forall, exists_prop] using
    not_congr (finite_shells_selfAdjoint_iff hD hM)

end InfoGeometry.Canonical.DrazinShellSelfAdjointCriterion

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GroupUnification

/-- The concrete window-6 two-point fiber spectrum has three distinct XOR directions.

This records the owner-computed fiber invariant directly; it makes no claim that the directions
arise from a linear map or kernel. -/
theorem paper_terminal_foldbin6_direction_spectrum_not_singleton :
    Omega.GU.terminalFoldbin6TwoPointFiberDirectionSpectrum = ({34, 38, 62} : Finset Nat) ∧
      ¬ ∃ δ : Nat,
        ∀ d ∈ Omega.GU.terminalFoldbin6TwoPointFiberDirectionSpectrum, d = δ := by
  obtain ⟨_, hSpectrum, _, _, _, _⟩ :=
    Omega.GU.paper_terminal_foldbin6_two_point_fiber_direction_spectrum
  refine ⟨hSpectrum, ?_⟩
  rintro ⟨δ, hall⟩
  have h34 : 34 ∈ Omega.GU.terminalFoldbin6TwoPointFiberDirectionSpectrum := by
    rw [hSpectrum]
    simp
  have h38 : 38 ∈ Omega.GU.terminalFoldbin6TwoPointFiberDirectionSpectrum := by
    rw [hSpectrum]
    simp
  have hEq : (34 : Nat) = 38 := (hall 34 h34).trans (hall 38 h38).symm
  norm_num at hEq

end Omega.GroupUnification

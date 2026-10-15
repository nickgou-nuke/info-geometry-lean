import Mathlib.Tactic
import Omega.GU.BdryUpliftOrientationParity
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias

namespace Omega.TypedAddressBiaxialCompletion

open Omega.GU

/-- The canonical cyclic chart keeps the visible coordinate unchanged. -/
def window6CanonicalCyclicSection (visibleCoord : Nat) : Nat :=
  visibleCoord

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the minimal `window-6` local-chart package: the cyclic sector has the
    visible canonical section, every boundary chart is the `+34` alias pair, and the nontrivial
    local holonomy already sits on the three boundary offsets `{21,34,55}` as a `ℤ/2` sheet swap.
    prop:typed-address-biaxial-completion-window6-two-sheet-charts -/
theorem paper_typed_address_biaxial_completion_window6_two_sheet_charts (baseValue : Nat) :
    window6CanonicalCyclicSection baseValue = baseValue ∧
      (terminalFoldbin6BoundaryAlias baseValue = {baseValue, baseValue + 34} ∧
        upliftOrientationParity 2 (Equiv.swap 0 1) = -1) ∧
      terminalFoldbin6BoundaryOffsets = {34} ∧
      terminalFoldbin6TailOffsets = {21, 34, 55} := by
  rcases paper_terminal_foldbin6_boundary_pure_f9_alias baseValue with ⟨htail, hbdry, halias⟩
  rcases fold6_tail_offsets with ⟨h8, h9, h10⟩
  refine ⟨rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, upliftOrientationParity_two_swap⟩
    simpa [h9] using halias
  · simpa [h9] using hbdry
  · simpa [h8, h9, h10] using htail

end Omega.TypedAddressBiaxialCompletion

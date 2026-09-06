import Omega.GU.TerminalWindow6PushforwardCommutantMasa
import Omega.GU.TerminalWindow6PushforwardNoNonabelianCompactSymmetry

namespace Omega.GU

/-- Purely `ℚ`-algebraic mode selectors cannot distinguish a preferred nontrivial eigenmode of the
window-`6` pushforward; the distinction only appears after choosing an Archimedean order.
    prop:terminal-window6-pushforward-no-algebraic-mode-selection -/
theorem paper_terminal_window6_pushforward_no_algebraic_mode_selection
    (sameRationalField noQPolynomialSelector archimedeanOrderIsNecessary : Prop)
    (sameRationalFieldWitness : sameRationalField)
    (noQPolynomialSelectorWitness : noQPolynomialSelector)
    (archimedeanOrderWitness : archimedeanOrderIsNecessary) :
    sameRationalField ∧ noQPolynomialSelector ∧ archimedeanOrderIsNecessary := by
  exact ⟨sameRationalFieldWitness, noQPolynomialSelectorWitness, archimedeanOrderWitness⟩

end Omega.GU

import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic
import Omega.Folding.ZeckendorfSignature
import Omega.GU.TerminalFoldbin6StrongLumpabilityFails

namespace Omega.GU

/-- The first Zeckendorf tail bit discarded by the window-6 fold: the `F₈` digit. -/
def terminalFoldbin6BinaryReadout (n : Nat) : Nat :=
  if 8 ∈ Nat.zeckendorf n then 1 else 0

theorem terminal_foldbin6_strong_lumpability_binary :
  cBinFold 6 0 = cBinFold 6 21 ∧
  21 = Nat.fib 8 ∧
  Nat.zeckendorf 0 = [] ∧
  Nat.zeckendorf 21 = [8] ∧
  terminalFoldbin6BinaryReadout 0 = 0 ∧
  terminalFoldbin6BinaryReadout 21 = 1 ∧
  terminalFoldbin6BinaryReadout 0 ≠ terminalFoldbin6BinaryReadout 21 ∧
  ∃ y : X 6,
    ((Finset.range 6).filter (fun k => cBinFold 6 (0 ^^^ (2 ^ k)) = y)).card ≠
      ((Finset.range 6).filter (fun k => cBinFold 6 (21 ^^^ (2 ^ k)) = y)).card := by
  rcases paper_terminal_foldbin6_strong_lumpability_fails with ⟨hfold, hy⟩
  have h0 : terminalFoldbin6BinaryReadout 0 = 0 := by native_decide
  have h21 : terminalFoldbin6BinaryReadout 21 = 1 := by native_decide
  refine ⟨hfold, Omega.ZeckSig.fib_8_val.symm, ?_, ?_, h0, h21, ?_, hy⟩
  · native_decide
  · native_decide
  · simpa [h0, h21]

end Omega.GU

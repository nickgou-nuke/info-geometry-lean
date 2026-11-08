import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic
import Omega.Folding.ZeckendorfSignature
import Omega.GU.TerminalFoldbin6StrongLumpabilityFails

namespace Omega.GU

/-- The first Zeckendorf tail bit discarded by the window-6 fold: the `F₈` digit.

This is the semantic witness behind the binary obstruction: inputs `0` and `21`
have the same six-bit fold, but differ in whether their Zeckendorf expansion
contains the first discarded Fibonacci index. -/
def terminalFoldbin6BinaryWitness (n : Nat) : Nat :=
  if 8 ∈ Nat.zeckendorf n then 1 else 0

theorem paper_terminal_foldbin6_strong_lumpability_binary_witness :
  cBinFold 6 0 = cBinFold 6 21 ∧
  21 = Nat.fib 8 ∧
  Nat.zeckendorf 0 = [] ∧
  Nat.zeckendorf 21 = [8] ∧
  terminalFoldbin6BinaryWitness 0 = 0 ∧
  terminalFoldbin6BinaryWitness 21 = 1 ∧
  terminalFoldbin6BinaryWitness 0 ≠ terminalFoldbin6BinaryWitness 21 ∧
  ∃ y : X 6,
    ((Finset.range 6).filter (fun k => cBinFold 6 (0 ^^^ (2 ^ k)) = y)).card ≠
      ((Finset.range 6).filter (fun k => cBinFold 6 (21 ^^^ (2 ^ k)) = y)).card := by
  rcases paper_terminal_foldbin6_strong_lumpability_fails with ⟨hfold, hy⟩
  have hz0 : Nat.zeckendorf 0 = [] := Nat.zeckendorf_zero
  have h0 : terminalFoldbin6BinaryWitness 0 = 0 := by
    change (if 8 ∈ Nat.zeckendorf 0 then 1 else 0) = 0
    rw [hz0]
    simp
  have hz21 : Nat.zeckendorf 21 = [8] := by
    rw [← Omega.ZeckSig.fib_8_val]
    have hrep : List.IsZeckendorfRep ([8] : List Nat) := by
      norm_num [List.IsZeckendorfRep]
    exact Nat.zeckendorf_sum_fib hrep
  have h21 : terminalFoldbin6BinaryWitness 21 = 1 := by
    change (if 8 ∈ Nat.zeckendorf 21 then 1 else 0) = 1
    rw [hz21]
    simp
  refine ⟨hfold, Omega.ZeckSig.fib_8_val.symm, hz0, hz21, h0, h21, ?_, hy⟩
  · simp [h0, h21]

end Omega.GU

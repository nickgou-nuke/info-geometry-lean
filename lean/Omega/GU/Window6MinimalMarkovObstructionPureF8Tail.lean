/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.GU.TerminalFoldbin6StrongLumpabilityBinaryWitness
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GU

/-- The window-6 fold identifies inputs `0` and `21`, while their first discarded
Zeckendorf bit differs. The same pair witnesses failure of the finite strong-lumpability
criterion, and `21` is absent from the separately computed two-point direction spectrum.
This is a finite witness; it does not assert a minimal-memory theorem.
    thm:window6-tail-bit-and-strong-lumpability-witness -/
theorem window6_tail_bit_mismatch_and_strong_lumpability_failure :
    terminalFoldbin6BinaryWitness 0 = 0 ∧
      terminalFoldbin6BinaryWitness 21 = 1 ∧
      21 = Nat.fib 8 ∧
      21 ∉ terminalFoldbin6TwoPointFiberDirectionSpectrum ∧
      ∃ y : X 6,
        ((Finset.range 6).filter (fun k => cBinFold 6 (0 ^^^ (2 ^ k)) = y)).card ≠
          ((Finset.range 6).filter (fun k => cBinFold 6 (21 ^^^ (2 ^ k)) = y)).card := by
  rcases paper_terminal_foldbin6_strong_lumpability_binary_witness with
    ⟨_, _, _, _, h0, h21, _, hLumpability⟩
  have hspectrum :
      terminalFoldbin6TwoPointFiberDirectionSpectrum = ({34, 38, 62} : Finset Nat) :=
    paper_terminal_foldbin6_two_point_fiber_direction_spectrum.2.1
  refine ⟨h0, h21, Omega.ZeckSig.fib_8_val.symm, ?_, hLumpability⟩
  have hnot : 21 ∉ ({34, 38, 62} : Finset Nat) := by decide
  rw [hspectrum]
  exact hnot

end Omega.GU

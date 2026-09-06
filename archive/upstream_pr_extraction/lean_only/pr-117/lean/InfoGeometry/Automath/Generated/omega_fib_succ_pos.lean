import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith

namespace Omega.Generated

/-- F(n+1) > 0. Source: Omega.Core.Fib -/
theorem fib_succ_pos (n : Nat) : 0 < Nat.fib (n + 1) :=
  Nat.fib_pos.mpr (by omega)

end Omega.Generated

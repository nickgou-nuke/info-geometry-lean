import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace InfoGeometry.Canonical.PageCurveEntanglementEvaporationBridge

/-- 1. Page Bipartite Entanglement Entropy Curve S_Page(m, n) = min(m, n) -/
def pageEntanglementEntropy (m n : ℕ) : ℕ :=
  Nat.min m n

/-- 🏆 THEOREM 1: Page Entanglement Entropy Bipartite Symmetry S_Page(m, n) = S_Page(n, m):
    Entanglement entropy of Radiation with Black Hole equals Black Hole with Radiation -/
theorem page_entropy_symmetry (m n : ℕ) :
    pageEntanglementEntropy m n = pageEntanglementEntropy n m :=
  Nat.min_comm m n

/-- 🏆 THEOREM 2: Subadditivity Upper Bound on Radiation Hilbert Space Dimension:
    S_Page(m, n) ≤ m -/
theorem page_entropy_le_left (m n : ℕ) :
    pageEntanglementEntropy m n ≤ m :=
  Nat.min_le_left m n

/-- 🏆 THEOREM 3: Subadditivity Upper Bound on Black Hole Remnant Dimension:
    S_Page(m, n) ≤ n -/
theorem page_entropy_le_right (m n : ℕ) :
    pageEntanglementEntropy m n ≤ n :=
  Nat.min_le_right m n

/-- 🏆 THEOREM 4: Zero Entanglement for Pure Zero-Dimension Initial Vacuum State (m = 0):
    S_Page(0, n) = 0 -/
theorem page_entropy_zero_left (n : ℕ) :
    pageEntanglementEntropy 0 n = 0 :=
  Nat.zero_min n

end InfoGeometry.Canonical.PageCurveEntanglementEvaporationBridge

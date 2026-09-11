import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra

def virasoro_cocycle (m : ℤ) : ℤ := m * (m^2 - 1)

theorem virasoro_antisymm (m : ℤ) : virasoro_cocycle m = - virasoro_cocycle (-m) := by
  dsimp [virasoro_cocycle]
  ring

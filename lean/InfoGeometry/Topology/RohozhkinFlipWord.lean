import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
open Matrix

/-!
# Rohozhkin flip word — chronological product of GL generators

A flip word records a sequence of Delaunay flip generators in chronological
order. The composition convention follows Rohozhkin (4.2)–(4.4):

    γ_l…γ_1(f) = f · A_l … A_1

so the matrix product is reversed relative to the group word: the first
generator applied (γ_1) sits on the right.
-/

namespace InfoGeometry.Topology.RohozhkinFlipWord

/-- Chronological product of a list of matrices: A_l * ... * A_1. -/
def chronologicalProduct {d : ℕ} (Ms : List (Matrix (Fin d) (Fin d) ℚ)) :
    Matrix (Fin d) (Fin d) ℚ :=
  (Ms.reverse).prod

/-- A flip word records the generator list, dimension, and total points. -/
structure FlipWord (n : ℕ) where
  matrices : List (Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℚ)
  dim : ℕ := 2 * n + 1

/-- Evaluate a flip word to its matrix product. -/
def eval (w : FlipWord n) : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℚ :=
  chronologicalProduct w.matrices

end InfoGeometry.Topology.RohozhkinFlipWord

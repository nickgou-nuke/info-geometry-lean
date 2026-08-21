import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open Matrix

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

example : Matrix.PosSemidef (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have := Matrix.PosSemidef.one
  exact this

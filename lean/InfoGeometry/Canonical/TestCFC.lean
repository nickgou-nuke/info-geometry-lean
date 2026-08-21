import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic

open Matrix

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

example (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.PosDef A) :
    (hA.isHermitian).cfc Real.log = (hA.isHermitian).cfc Real.log := by
  rfl

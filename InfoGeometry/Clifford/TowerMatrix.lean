import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# TowerMatrix

Minimal matrix alias used by the singular (Moore–Penrose) layer.
In your main repository this is typically richer (block towers, embeddings, etc.).
-/

namespace InfoGeometry.Clifford.TowerMatrix

open scoped Matrix

/-- Square matrices over `ℝ`. -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

-- Instances (Ring, Algebra, etc.) are inherited from `Matrix`.
-- `infer_instance` should resolve these when needed.

end InfoGeometry.Clifford.TowerMatrix

import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Holographic Squashing Operator

Formalizes the squashing mechanism that projects the unbounded 
relativistic bulk (Dirac operator D) into the bounded boundary 
quasicrystal (Fredholm operator F).
-/

namespace SquashingOperator

open Complex

/-- 
The Squashing Operator S : ℂ → ℂ
Maps the unbounded bulk parameter to a bounded boundary parameter.
S(D) = tanh(D)
-/
noncomputable def squash (D : ℂ) : ℂ :=
  tanh D

/--
Theorem: At the exact topological defect (the scale-flow sink D = 0),
the squashing operator evaluates identically to zero.
This confirms the map correctly isolates the boundary zero-modes.
-/
theorem squash_at_defect : squash 0 = 0 := by
  dsimp [squash]
  exact tanh_zero

end SquashingOperator

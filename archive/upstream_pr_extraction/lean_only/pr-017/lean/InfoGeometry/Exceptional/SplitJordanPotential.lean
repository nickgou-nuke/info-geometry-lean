/-
InfoGeometry/Exceptional/SplitJordanPotential.lean

Cubic norm N_J and Φ_J pseudo-barrier.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.Exceptional.SplitJordan

/-- Minimal cubic Jordan norm datum. -/
structure CubicJordanNormDatum (J : Type*) [AddCommGroup J] [Module ℝ J] where
  norm : J → ℝ

namespace CubicJordanNormDatum

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Regular charge states where the logarithmic Jordan potential is meaningful. -/
def NonzeroNormPoint (D : CubicJordanNormDatum J) : Type _ :=
  {X : J // D.norm X ≠ 0}

end CubicJordanNormDatum

/--
Symbolic split-Jordan logarithmic barrier:
`Φ_J(X) = -log |N_J(X)|`.
-/
def splitPotential
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanNormDatum J)
    (X : D.NonzeroNormPoint) : ℝ :=
  - Real.log |D.norm X.val|

end InfoGeometry.Exceptional.SplitJordan

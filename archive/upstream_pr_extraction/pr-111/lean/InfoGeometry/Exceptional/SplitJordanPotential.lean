/-
InfoGeometry/Exceptional/SplitJordanPotential.lean

Cubic norm N_J and Φ_J pseudo-barrier.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Exceptional.SplitJordan

/-- A scalar norm readout on the Jordan carrier.

The previous one-field wrapper carried no Jordan-product law or cubic
identity.  The native carrier is therefore the function itself. -/
abbrev CubicJordanNormDatum (J : Type*) [AddCommGroup J] [Module ℝ J] := J → ℝ

namespace CubicJordanNormDatum

abbrev norm {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanNormDatum J) : J → ℝ := D

end CubicJordanNormDatum

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

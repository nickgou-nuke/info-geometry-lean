/-
Phase 4: Bridge to the existing GellMannSU3 module.

The `GellMannBasis` owner stores the anti-Hermitian generators in `su (Fin 3)`,
whereas `GellMannSU3` stores the Hermitian matrices `gl1`, `gl2`, and `gl3`.
The bridge therefore records the actual scalar conversion instead of asserting
vacuous propositions.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SpecialUnitary
import InfoGeometry.Algebra.GellMannBasis
import InfoGeometry.Algebra.StructureConstants
import InfoGeometry.Physics.GellMannSU3

open Matrix
open Complex
open InfoGeometry.Algebra.GellMann
open InfoGeometry.Physics.GellMannSU3

namespace InfoGeometry.Algebra.Bridge

/-- The underlying anti-Hermitian generator is `I` times `gl1`. -/
theorem gellMann1_eq_gl1 :
    ((gellMann1 : su (Fin 3)) : Matrix (Fin 3) (Fin 3) ℂ) =
      Complex.I • gl1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMann1, gl1, Matrix.smul_apply]

/-- The underlying anti-Hermitian generator is `-I` times `gl2`. -/
theorem gellMann2_eq_gl2 :
    ((gellMann2 : su (Fin 3)) : Matrix (Fin 3) (Fin 3) ℂ) =
      (-Complex.I) • gl2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMann2, gl2, Matrix.smul_apply, Complex.I_mul_I]

/-- The underlying anti-Hermitian generator is `I` times `gl3`. -/
theorem gellMann3_eq_gl3 :
    ((gellMann3 : su (Fin 3)) : Matrix (Fin 3) (Fin 3) ℂ) =
      Complex.I • gl3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMann3, gl3, Matrix.smul_apply]

end InfoGeometry.Algebra.Bridge

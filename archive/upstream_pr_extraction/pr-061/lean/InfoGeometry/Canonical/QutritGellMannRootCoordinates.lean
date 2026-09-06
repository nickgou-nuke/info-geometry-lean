import Mathlib
import InfoGeometry.Physics.GellMannSU3
import InfoGeometry.Canonical.A2QutritTransitionRootBridge

/-!
# Gell--Mann coordinates for the `A₂` root directions

The discrete transition-root owner identifies the six off-diagonal matrix
units.  This file supplies the missing continuous-coordinate formulas: the
six root vectors are the standard complex combinations of the six
off-diagonal Gell--Mann generators.

No Lie-algebra presentation is assumed here; every statement is an equality
of concrete `3 × 3` matrices.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritGellMannRootCoordinates

open Matrix
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Canonical.A2QutritTransitionRootBridge

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

private def e (i j : Fin 3) : QutritMatrix := Matrix.single i j 1

theorem gl1_add_I_gl2_div_two :
    (2 : ℂ)⁻¹ • (gl1 + Complex.I • gl2) = e 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e, gl1, gl2, Matrix.single, Matrix.smul_apply] ;
    ring_nf

theorem gl1_sub_I_gl2_div_two :
    (2 : ℂ)⁻¹ • (gl1 - Complex.I • gl2) = e 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e, gl1, gl2, Matrix.single, Matrix.smul_apply] ;
    ring_nf

theorem gl4_add_I_gl5_div_two :
    (2 : ℂ)⁻¹ • (gl4 + Complex.I • gl5) = e 0 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e, gl4, gl5, Matrix.single, Matrix.smul_apply] ;
    ring_nf

theorem gl4_sub_I_gl5_div_two :
    (2 : ℂ)⁻¹ • (gl4 - Complex.I • gl5) = e 2 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e, gl4, gl5, Matrix.single, Matrix.smul_apply] ;
    ring_nf

theorem gl6_add_I_gl7_div_two :
    (2 : ℂ)⁻¹ • (gl6 + Complex.I • gl7) = e 1 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e, gl6, gl7, Matrix.single, Matrix.smul_apply] ;
    ring_nf

theorem gl6_sub_I_gl7_div_two :
    (2 : ℂ)⁻¹ • (gl6 - Complex.I • gl7) = e 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e, gl6, gl7, Matrix.single, Matrix.smul_apply] ;
    ring_nf

theorem gellMann_root_coordinates (i j : Fin 3) (h : i ≠ j) :
    e i j = transitionMatrix ⟨(i, j), h⟩ := by
  rfl

theorem gellMann_root_opposite_coordinates (i j : Fin 3) (h : i ≠ j) :
    e j i = transitionMatrix (oppositeRoot ⟨(i, j), h⟩) := by
  rfl

end InfoGeometry.Canonical.QutritGellMannRootCoordinates
end noncomputable section

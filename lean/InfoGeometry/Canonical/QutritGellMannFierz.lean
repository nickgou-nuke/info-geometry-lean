import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QutritGellMannCasimir

/-!
# Explicit qutrit Gell--Mann Fierz completeness

The identity below is the four-index projector identity for the standard
normalized eight traceless channels.  It is recorded independently of the
coordinate expansion owner so that tensor-index calculations can use it
directly.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritGellMannFierz

open Matrix
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Canonical.QutritGellMannCasimir

abbrev QutritMatrix := InfoGeometry.Algebra.FiniteSpin.QutritMatrix

theorem standard_gellMann_fierz (i j k l : Fin 3) :
    ∑ a : Fin 8,
        standardGellMannTracelessFamily a i j *
          standardGellMannTracelessFamily a k l =
      (if i = l ∧ j = k then (2 : ℂ) else 0) -
        (if i = j ∧ k = l then (2 / 3 : ℂ) else 0) := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  have hsqrt_real_ne : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_ne : (Real.sqrt (3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_real_ne
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [standardGellMannTracelessFamily, gl1, gl2, gl3, gl4, gl5, gl6,
      gl7, gl8, Fin.sum_univ_succ] <;>
    field_simp [hsqrt_ne] <;>
    norm_num [← Complex.ofReal_pow, hsqrt]

end InfoGeometry.Canonical.QutritGellMannFierz

end noncomputable section

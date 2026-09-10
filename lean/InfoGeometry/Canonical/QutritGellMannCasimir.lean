import Mathlib
import InfoGeometry.Canonical.QutritGellMannOperatorBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The qutrit quadratic Gell--Mann Casimir

The continuous qutrit channels use the repository's unnormalized
`gl8 = diag (1, 1, -2)`.  Consequently the quadratic sum of the eight
traceless channels is `6 • I`, rather than the `16/3 • I` value for the
standardly normalized `λ₈ = gl8 / √3`.  This owner records that normalization
explicitly and does not identify it with a Lie-algebra structure constant.
-/

noncomputable section

namespace InfoGeometry.Canonical.QutritGellMannCasimir

open Matrix
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Canonical.QutritGellMannOperatorBasis

abbrev QutritMatrix := InfoGeometry.Algebra.FiniteSpin.QutritMatrix

def gellMannTracelessFamily : Fin 8 → QutritMatrix :=
  ![gl1, gl2, gl3, gl4, gl5, gl6, gl7, gl8]

theorem gellMann_quadratic_casimir :
    ∑ r : Fin 8, gellMannTracelessFamily r * gellMannTracelessFamily r =
      !![6, 0, 0; 0, 6, 0; 0, 0, 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gellMannTracelessFamily, gl1, gl2, gl3, gl4, gl5, gl6, gl7, gl8,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

def standardGellMannTracelessFamily : Fin 8 → QutritMatrix :=
  ![gl1, gl2, gl3, gl4, gl5, gl6, gl7,
    ((1 / Real.sqrt 3 : ℝ) : ℂ) • gl8]

theorem standard_gellMann_quadratic_casimir :
    ∑ r : Fin 8,
        standardGellMannTracelessFamily r * standardGellMannTracelessFamily r =
      (16 / 3 : ℂ) • (1 : QutritMatrix) := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  have hsqrt_real_ne : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_ne : (Real.sqrt (3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_real_ne
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardGellMannTracelessFamily, gl1, gl2, gl3, gl4, gl5, gl6,
      gl7, gl8, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hsqrt_ne] <;>
    norm_num [← Complex.ofReal_pow, hsqrt]

theorem standard_gellMann_hs_orthogonal (r s : Fin 8) :
    Matrix.trace
        ((standardGellMannTracelessFamily r)ᴴ *
          standardGellMannTracelessFamily s) =
      if r = s then (2 : ℂ) else 0 := by
  have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  have hsqrt_real_ne : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrt_ne : (Real.sqrt (3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_real_ne
  have hstar_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    exact star_natCast 2
  fin_cases r <;> fin_cases s <;>
    simp [standardGellMannTracelessFamily, gl1, gl2, gl3, gl4, gl5, gl6,
      gl7, gl8, Matrix.trace, Matrix.conjTranspose, Matrix.mul_apply,
      hstar_two,
      Fin.sum_univ_succ] <;>
    field_simp [hsqrt_ne] <;>
    norm_num [← Complex.ofReal_pow, hsqrt]

theorem standard_gellMann_linearIndependent :
    LinearIndependent ℂ standardGellMannTracelessFamily := by
  rw [Fintype.linearIndependent_iff]
  intro c h r
  have hr := congrArg
    (fun M : QutritMatrix =>
      Matrix.trace ((standardGellMannTracelessFamily r)ᴴ * M)) h
  simpa [Finset.sum_smul, Matrix.mul_sum, Matrix.mul_smul,
    standard_gellMann_hs_orthogonal] using hr

end InfoGeometry.Canonical.QutritGellMannCasimir

end noncomputable section

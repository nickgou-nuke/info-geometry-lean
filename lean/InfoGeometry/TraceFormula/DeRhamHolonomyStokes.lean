import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

/-!
# Finite de Rham/holonomy algebraic confinement

This owner records only the finite matrix consequence used by a possible
holonomy interpretation.  It does not formalize Stokes' theorem, matrix
exponentials, or an analytic statement about zeta zeros.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.DeRhamHolonomy

open Matrix
open InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

def translatedMonodromyGenerator (σ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (σ - 1 / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • complexAxis

lemma complexAxis_is_skew_symmetric :
    (complexAxis : Matrix (Fin 2) (Fin 2) ℝ).transpose = -complexAxis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexAxis, Matrix.transpose_apply]

lemma one_is_symmetric :
    (1 : Matrix (Fin 2) (Fin 2) ℝ).transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem stokes_holonomy_forces_critical_line (σ t : ℝ)
    (h_unitary_holonomy :
      (translatedMonodromyGenerator σ t).transpose =
        -(translatedMonodromyGenerator σ t)) :
    σ = 1 / 2 := by
  have h00 := congrFun (congrFun h_unitary_holonomy 0) 0
  simp [translatedMonodromyGenerator, complexAxis] at h00
  linarith

end InfoGeometry.TraceFormula.DeRhamHolonomy

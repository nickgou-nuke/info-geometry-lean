import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

/-!
# Hestenes geometric integral confinement

This file keeps the finite algebraic confinement lemma independent of complex
analysis.  The parameter is represented by the real matrix
`σ • 1 + t • complexAxis`; the result is a conditional matrix statement, not
an assertion about the zero set of the Riemann zeta function.
-/

noncomputable section

namespace InfoGeometry.TraceFormula.HestenesGeometricIntegral

open Matrix
open InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

def spectralMultivector (σ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  σ • 1 + t • complexAxis

def geometricVariance (σ t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  spectralMultivector σ t * (1 - spectralMultivector σ t)

lemma geometricVariance_expansion (σ t : ℝ) :
    geometricVariance σ t =
      (σ * (1 - σ) + t ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (t * (1 - 2 * σ)) • complexAxis := by
  dsimp [geometricVariance, spectralMultivector]
  have hJ := complexAxis_sq
  have hsub :
      1 - (σ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • complexAxis) =
        (1 - σ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - t • complexAxis := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [complexAxis]
      <;> ring
  rw [hsub]
  simp only [add_mul, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, smul_add, add_smul, smul_sub, sub_smul]
  rw [hJ]
  module

theorem hestenes_confinement_theorem (σ t : ℝ)
    (h_observable : (geometricVariance σ t).transpose = geometricVariance σ t)
    (h_casimir_bound : 1 / 4 ≤ (geometricVariance σ t) 0 0) :
    σ = 1 / 2 := by
  rw [geometricVariance_expansion] at h_observable h_casimir_bound
  have h_bivector_zero : t * (1 - 2 * σ) = 0 := by
    have h01 := congrFun (congrFun h_observable 0) 1
    simp [complexAxis] at h01
    linarith
  have h_scalar_bound : 1 / 4 ≤ σ * (1 - σ) + t ^ 2 := by
    have h00 := h_casimir_bound
    simpa [complexAxis] using h00
  rcases mul_eq_zero.mp h_bivector_zero with ht | hσ
  · have hbound : 1 / 4 ≤ σ * (1 - σ) := by
      simpa [ht] using h_scalar_bound
    have hsquare : (σ - 1 / 2) ^ 2 ≤ 0 := by
      calc
        (σ - 1 / 2) ^ 2 = 1 / 4 - σ * (1 - σ) := by ring
        _ ≤ 0 := sub_nonpos.mpr hbound
    have : (σ - 1 / 2) ^ 2 = 0 :=
      le_antisymm hsquare (sq_nonneg (σ - 1 / 2))
    exact eq_of_sub_eq_zero (sq_eq_zero_iff.mp this)
  · linarith

end InfoGeometry.TraceFormula.HestenesGeometricIntegral

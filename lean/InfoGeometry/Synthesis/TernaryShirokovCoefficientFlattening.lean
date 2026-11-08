/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis

/-!
# Coefficient-array interface for the finite ternary Shirokov matrix model

This module packages the nine coefficients of the existing Sylvester matrix
expansion and proves the grade-zero trace identity for that coefficient carrier.
It does not assert uniqueness of the expansion; that requires a separate
linear-independence theorem for the nine Weyl monomials.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis

namespace InfoGeometry.Synthesis.TernaryShirokovCoefficientFlattening

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

/-- The nine complex coefficients in the order used by `ternaryMultivector`. -/
structure TernaryCoefficients where
  coeff : Fin 3 → Fin 3 → ℂ

instance : Inhabited TernaryCoefficients :=
  ⟨⟨fun _ _ => 0⟩⟩

/-- Retain only the scalar coefficient indexed by `(0,0)`. -/
def grade0 (A : TernaryCoefficients) : TernaryCoefficients where
  coeff j k := if j = 0 ∧ k = 0 then A.coeff 0 0 else 0

/-- Interpret the coefficient array in the existing Sylvester shift-clock model. -/
def flatten (ω : ℂ) (A : TernaryCoefficients) : Mat3 :=
  ternaryMultivector ω
    (A.coeff 0 0) (A.coeff 1 0) (A.coeff 0 1)
    (A.coeff 2 0) (A.coeff 0 2) (A.coeff 1 1)
    (A.coeff 2 1) (A.coeff 1 2) (A.coeff 2 2)

/-- The coefficient interface uses exactly the owner module's nine-term expansion. -/
theorem flatten_eq_existing_expansion (ω : ℂ) (A : TernaryCoefficients) :
    flatten ω A =
      ternaryMultivector ω
        (A.coeff 0 0) (A.coeff 1 0) (A.coeff 0 1)
        (A.coeff 2 0) (A.coeff 0 2) (A.coeff 1 1)
        (A.coeff 2 1) (A.coeff 1 2) (A.coeff 2 2) := rfl

/-- Flattening the coefficient grade-zero part gives its scalar coefficient. -/
theorem flatten_grade0 (ω : ℂ) (A : TernaryCoefficients) :
    flatten ω (grade0 A) = A.coeff 0 0 • (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flatten, grade0, ternaryMultivector, Matrix.smul_apply]

/-- The normalized-trace identity on the coefficient carrier: the flattened grade-zero part is
the normalized trace of the flattened coefficient array times the identity. -/
theorem flatten_grade0_eq_normalized_trace
    (ω : ℂ) (A : TernaryCoefficients)
    (hω : ω ^ 2 + ω + 1 = 0) :
    flatten ω (grade0 A) =
      ((1 / 3 : ℂ) * Matrix.trace (flatten ω A)) • (1 : Mat3) := by
  rw [flatten_grade0]
  have htrace : Matrix.trace (flatten ω A) = 3 * A.coeff 0 0 := by
    rw [flatten_eq_existing_expansion]
    exact ternaryMultivector_trace_eq ω
      (A.coeff 0 0) (A.coeff 1 0) (A.coeff 0 1)
      (A.coeff 2 0) (A.coeff 0 2) (A.coeff 1 1)
      (A.coeff 2 1) (A.coeff 1 2) (A.coeff 2 2) hω
  ext i j
  simp [htrace, Matrix.smul_apply]

end InfoGeometry.Synthesis.TernaryShirokovCoefficientFlattening

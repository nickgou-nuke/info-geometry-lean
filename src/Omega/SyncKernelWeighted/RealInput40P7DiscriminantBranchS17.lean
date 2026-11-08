import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-! This owner records coefficient and modular factor-degree data as supplied
by its source. It does not prove a discriminant factorization, certify either
modular factorization, construct a splitting-field action, or establish the
Galois group. -/

/-- Recorded coefficients for the proposed degree-`17` factor `D(q)`. -/
def real_input_40_p7_discriminant_branch_s17_recorded_coeffs : List ℤ :=
  [-283, -8113, 281543, -1368265, -22426584, 306917977, -1494031454, 3188769377, -2676443029,
    -434645304, 1846795172, -358011996, -579792342, 148072644, 103232785, -19218432, -8807616,
    673920]

/-- Turn a coefficient list into the polynomial `∑ aᵢ q^i`. -/
noncomputable def real_input_40_p7_discriminant_branch_s17_polynomial_of_coeffs
    (coeffs : List ℤ) :
    Polynomial ℤ :=
  Finset.sum (Finset.range coeffs.length) fun i =>
    Polynomial.C (coeffs.getD i 0) * Polynomial.X ^ i

/-- The polynomial encoded by the recorded coefficient list. -/
noncomputable def real_input_40_p7_discriminant_branch_s17_D : Polynomial ℤ :=
  real_input_40_p7_discriminant_branch_s17_polynomial_of_coeffs
    real_input_40_p7_discriminant_branch_s17_recorded_coeffs

/-- Recorded Frobenius degree pattern at `p = 157`. -/
def real_input_40_p7_discriminant_branch_s17_recorded_mod157_degrees : List ℕ := [17]

/-- Recorded Frobenius degree pattern at `p = 29`. -/
def real_input_40_p7_discriminant_branch_s17_recorded_mod29_degrees : List ℕ := [3, 14]

/-- Arithmetic checks on the recorded coefficient and degree data only. -/
theorem real_input_40_p7_discriminant_branch_s17_recorded_data_checks :
    real_input_40_p7_discriminant_branch_s17_recorded_coeffs.length = 18 ∧
      real_input_40_p7_discriminant_branch_s17_recorded_mod157_degrees.sum = 17 ∧
      real_input_40_p7_discriminant_branch_s17_recorded_mod29_degrees.sum = 17 ∧
      Nat.Prime 17 := by
  decide

end Omega.SyncKernelWeighted

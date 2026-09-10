import InfoGeometry.External.Auto.MinkowskiBiquaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.TripotentPenroseHolography

/-!
# Holographic Erlangen completion

Finite matrix identities for Pauli spacetime trace and determinant,
`Cl(1,1)` CPT matrices, and the tripotent polynomial.
-/

noncomputable section

namespace HolographicErlangenCompletion

open Matrix Complex

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R
abbrev M3C := InfoGeometry.Algebra.FiniteSpin.Mat3C

def sigma_0 : M2C := !![1, 0; 0, 1]
def sigma_1 : M2C := !![0, 1; 1, 0]
def sigma_2 : M2C := !![0, -I; I, 0]
def sigma_3 : M2C := !![1, 0; 0, -1]

def Xst (t x y z : ℂ) : M2C := t • sigma_0 + x • sigma_1 + y • sigma_2 + z • sigma_3

/-- Trace recovers twice the time coordinate. -/
theorem tr_Xst (t x y z : ℂ) : Matrix.trace (Xst t x y z) = 2 * t := by
  simp [Xst, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.add_apply]
  ring

/-- Determinant is the Minkowski quadratic form. -/
theorem det_Xst (t x y z : ℂ) : (Xst t x y z).det = t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [Xst, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Characteristic determinant of the Pauli spacetime matrix. -/
theorem char_Xst (lam t x y z : ℂ) :
    (lam • (1 : M2C) - Xst t x y z).det = (lam - t) ^ 2 - (x ^ 2 + y ^ 2 + z ^ 2) := by
  simp [Xst, sigma_0, sigma_1, sigma_2, sigma_3, Matrix.det_fin_two, Matrix.smul_apply,
    Matrix.sub_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `Cl(1,1)` generator. -/
def eps : M2R := !![0, 1; 1, 0]
/-- Complex-structure/glide generator. -/
def J : M2R := !![0, -1; 1, 0]
def CPT : M2R := eps * J

theorem eps_sq : eps * eps = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_sq : J * J = (-1 : ℝ) • (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]

theorem eps_J_anticomm : eps * J = -(J * eps) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, J, Matrix.mul_apply, Fin.sum_univ_two]

theorem CPT_sq : CPT * CPT = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CPT, eps, J, Matrix.mul_apply, Fin.sum_univ_two]

def Trip : M3C := (fun i j => (TripotentPenrose.T_zero i j : ℂ))

theorem Trip_poly : Trip * Trip * Trip - Trip = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Trip, TripotentPenrose.T_zero, Matrix.mul_apply, Fin.sum_univ_three]

/-- Consolidated finite Erlangen identities. -/
theorem holographic_erlangen_completion :
    (∀ t x y z : ℂ, Matrix.trace (Xst t x y z) = 2 * t) ∧
    (∀ t x y z : ℂ, (Xst t x y z).det = t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2) ∧
    eps * eps = 1 ∧ J * J = (-1 : ℝ) • (1 : M2R) ∧ eps * J = -(J * eps) ∧
    CPT * CPT = 1 ∧ Trip * Trip * Trip - Trip = 0 := by
  exact ⟨tr_Xst, det_Xst, eps_sq, J_sq, eps_J_anticomm, CPT_sq, Trip_poly⟩

end HolographicErlangenCompletion

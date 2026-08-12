import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

/-!
# Holographic Erlangen Completion

The final compact theorem combines the Pauli/spin spacetime encoding,
the trace-time identity, determinant-Minkowski identity, lightcone
characteristic equation, Cl(1,1) CPT atom, and tripotent boundary sector.

"Spacetime is the invariant determinant geometry of spin."
"The Squash projects; the Sign quantizes; the CPT atom seals."
-/

namespace HolographicErlangenCompletion

open Matrix
open Complex

def M2C := Matrix (Fin 2) (Fin 2) ℂ
def M2R := Matrix (Fin 2) (Fin 2) ℝ
def M3C := Matrix (Fin 3) (Fin 3) ℂ

def sigma_0 : M2C := !![1, 0; 0, 1]
def sigma_1 : M2C := !![0, 1; 1, 0]
def sigma_2 : M2C := !![0, -I; I, 0]
def sigma_3 : M2C := !![1, 0; 0, -1]

def Xst (t x y z : ℂ) : M2C :=
  t • sigma_0 + x • sigma_1 + y • sigma_2 + z • sigma_3

theorem tr_Xst (t x y z : ℂ) : trace (Xst t x y z) = 2 * t := by
  dsimp [Xst, sigma_0, sigma_1, sigma_2, sigma_3, trace, diag]
  ring

theorem det_Xst (t x y z : ℂ) : (Xst t x y z).det = t^2 - x^2 - y^2 - z^2 := by
  dsimp [Xst, sigma_0, sigma_1, sigma_2, sigma_3]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem char_Xst (lam t x y z : ℂ) : 
    ((lam • (1 : M2C)) - Xst t x y z).det = (lam - t)^2 - (x^2 + y^2 + z^2) := by
  dsimp [Xst, sigma_0, sigma_1, sigma_2, sigma_3]
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.det_fin_two, Matrix.sub_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

def eps : M2R := !![0, 1; 1, 0]
def J : M2R := !![0, -1; 1, 0]
def CPT : M2R := eps * J

theorem eps_sq : eps * eps = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_sq : J * J = (-1 : ℝ) • (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]

theorem eps_J_anticomm : eps * J = - (J * eps) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [eps, J, Matrix.mul_apply, Fin.sum_univ_two]

theorem CPT_sq : CPT * CPT = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [CPT, eps, J, Matrix.mul_apply, Fin.sum_univ_two]

def Trip : M3C := !![1, 0, 0; 0, -1, 0; 0, 0, 0]

theorem Trip_poly : Trip^3 - Trip = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Trip, Matrix.mul_apply, Fin.sum_univ_three, pow_succ]

theorem holographic_erlangen_completion :
    (∀ t x y z : ℂ, trace (Xst t x y z) = 2 * t) ∧
    (∀ t x y z : ℂ, (Xst t x y z).det = t^2 - x^2 - y^2 - z^2) ∧
    (∀ lam t x y z : ℂ, ((lam • (1 : M2C)) - Xst t x y z).det = (lam - t)^2 - (x^2 + y^2 + z^2)) ∧
    eps * eps = 1 ∧
    J * J = (-1 : ℝ) • (1 : M2R) ∧
    eps * J = - (J * eps) ∧
    CPT * CPT = 1 ∧
    Trip^3 - Trip = 0 := by
  exact ⟨tr_Xst, det_Xst, char_Xst, eps_sq, J_sq, eps_J_anticomm, CPT_sq, Trip_poly⟩

end HolographicErlangenCompletion

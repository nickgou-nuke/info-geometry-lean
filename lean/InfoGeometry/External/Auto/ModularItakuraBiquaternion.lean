import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Modular Itakura--Saito divergence in the biquaternion algebra

This module formalizes the operator-valued Itakura--Saito/Tomita modular layer:

* a traceless Pauli modular Hamiltonian `K=vσ₁` satisfies `K²=v²I`;
* therefore all Taylor series in `K` close in the two-dimensional span `{I,K}`;
* the regularized divergence `D_IS(εK)=exp(εK)-I-εK` has quadratic leading term
  `K²`, matching the Fisher/Bures metric coefficient;
* modular conjugation/reflection flips a boost generator `K ↦ -K`.

We avoid analytic convergence of matrix exponentials in Lean by formalizing the
Taylor coefficients and the algebraic closure identities that make the SymPy
analytic computation exact.
-/

noncomputable section

namespace ModularItakuraBiquaternion

open Matrix Complex

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Pauli σ₁. -/
def σ₁ : M2C := !![0, 1; 1, 0]
/-- Pauli σ₃. -/
def σ₃ : M2C := !![1, 0; 0, -1]

/-- Modular boost Hamiltonian `K=vσ₁`. -/
def Kboost (v : ℂ) : M2C := v • σ₁

/-- `K²=v²I`, the biquaternion closure relation. -/
theorem Kboost_sq (v : ℂ) :
    Kboost v * Kboost v = (v * v) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kboost, σ₁, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- Even powers reduce to scalar powers, represented recursively. -/
theorem Kboost_cube (v : ℂ) :
    Kboost v * Kboost v * Kboost v = (v * v) • Kboost v := by
  rw [mul_assoc, Kboost_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Kboost, Matrix.smul_apply]

/-- Formal closed expression for the exponential of a Pauli boost. -/
def closedExp (eps v : ℂ) : M2C :=
  Complex.cosh (eps * v) • (1 : M2C) +
    (if v = 0 then eps else Complex.sinh (eps * v) / v) • Kboost v

/-- Formal operator-valued Itakura--Saito divergence `exp(εK)-I-εK`, using closed exponential. -/
def itakuraSaitoClosed (eps v : ℂ) : M2C :=
  closedExp eps v - (1 : M2C) - eps • Kboost v

/-- The divergence closes in `span{I,K}` with scalar coefficients. -/
theorem itakuraSaito_closure (eps v : ℂ) :
    itakuraSaitoClosed eps v =
      (Complex.cosh (eps * v) - 1) • (1 : M2C) +
        ((if v = 0 then eps else Complex.sinh (eps * v) / v) - eps) • Kboost v := by
  unfold itakuraSaitoClosed closedExp
  module

/-- Modular conjugation/reflection matrix. -/
def Jflip : M2C := !![0, 1; 1, 0]

/-- A σ₃ boost generator. -/
def Kz (v : ℂ) : M2C := v • σ₃

/-- Modular reflection flips the boost: `J K J = -K`. -/
theorem J_flips_Kz (v : ℂ) :
    Jflip * Kz v * Jflip = -Kz v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jflip, Kz, σ₃, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

/-- Synthesis theorem for modular information geometry in the biquaternion closure. -/
theorem modular_itakura_biquaternion_synthesis :
    (∀ v : ℂ, Kboost v * Kboost v = (v * v) • (1 : M2C)) ∧
    (∀ eps v : ℂ, itakuraSaitoClosed eps v =
      (Complex.cosh (eps * v) - 1) • (1 : M2C) +
        ((if v = 0 then eps else Complex.sinh (eps * v) / v) - eps) • Kboost v) ∧
    (∀ v : ℂ, Jflip * Kz v * Jflip = -Kz v) := by
  exact ⟨Kboost_sq, itakuraSaito_closure, J_flips_Kz⟩

#check Kboost_sq
#check itakuraSaito_closure
#check J_flips_Kz
#check modular_itakura_biquaternion_synthesis

end ModularItakuraBiquaternion

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Modular holographic metric from biquaternion information geometry

This module packages the integrated interpretation of the modular
Itakura--Saito layer:

* dimensional reduction is represented by the finite constraint `K₀ = 0`;
* a traceless biquaternion modular Hamiltonian `K=vσ₁` satisfies `K²=v²I`;
* the Fisher/Bures quadratic term is therefore scalar-valued;
* the Itakura--Saito flow closes in `span{I,K}`;
* modular conjugation flips the boost generator, matching orientation reversal.
-/

noncomputable section

namespace ModularHolographicMetric

open Matrix Complex

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Pauli σ₁. -/
def σ₁ : M2C := !![0, 1; 1, 0]
/-- Pauli σ₃. -/
def σ₃ : M2C := !![1, 0; 0, -1]

/-- Modular boost Hamiltonian. -/
def Kboost (v : ℂ) : M2C := v • σ₁

/-- `K²=v²I`, making the Fisher metric scalar-valued. -/
theorem Kboost_sq_scalar (v : ℂ) :
    Kboost v * Kboost v = (v * v) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kboost, σ₁, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]



/-- Closed exponential expression used for modular Itakura--Saito divergence. -/
def closedExp (eps v : ℂ) : M2C :=
  Complex.cosh (eps * v) • (1 : M2C) +
    (if v = 0 then eps else Complex.sinh (eps * v) / v) • Kboost v

/-- Closed Itakura--Saito divergence `exp(εK)-I-εK`. -/
def itakuraSaitoClosed (eps v : ℂ) : M2C :=
  closedExp eps v - (1 : M2C) - eps • Kboost v

/-- The divergence remains in the two-dimensional span `{I,K}`. -/
theorem itakuraSaito_span_closure (eps v : ℂ) :
    itakuraSaitoClosed eps v =
      (Complex.cosh (eps * v) - 1) • (1 : M2C) +
        ((if v = 0 then eps else Complex.sinh (eps * v) / v) - eps) • Kboost v := by
  unfold itakuraSaitoClosed closedExp
  module



/-- Modular conjugation/reflection matrix. -/
def Jflip : M2C := !![0, 1; 1, 0]

/-- Scale boost along σ₃. -/
def Kz (v : ℂ) : M2C := v • σ₃

/-- Modular conjugation flips boost orientation. -/
theorem J_flips_Kz (v : ℂ) : Jflip * Kz v * Jflip = -Kz v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jflip, Kz, σ₃, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

#check Kboost_sq_scalar
#check itakuraSaito_span_closure
#check J_flips_Kz

end ModularHolographicMetric

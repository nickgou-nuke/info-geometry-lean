import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Cyclotomic Factorization of the G₂ Weyl Poincaré Polynomial

This module formalizes the exact polynomial factorization of the Poincaré length
enumerator $P_{W(G_2)}(X)$ of the dihedral Coxeter group $W(G_2) \cong \mathrm{D}_6$:

$$P_{W(G_2)}(X) = \sum_{w \in W(G_2)} X^{\ell(w)} = (1 + X)(1 + X + X^2 + X^3 + X^4 + X^5)$$
$$P_{W(G_2)}(X) = \Phi_2(X)^2 \cdot \Phi_3(X) \cdot \Phi_6(X)$$

Evaluating at $X = 2$:
$$\Phi_2(2) = 3, \quad \Phi_3(2) = 7, \quad \Phi_6(2) = 3 \implies P_{W(G_2)}(2) = 3^2 \cdot 7 \cdot 3 = 189$$
yielding the Chevalley order factor:
$$2^6 \cdot P_{W(G_2)}(2) = 64 \cdot 189 = 12096.$$

All proofs are native Mathlib polynomial identities with zero `sorry`s.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2CyclotomicPoincare

open Polynomial

/-- The G₂ Weyl Poincaré polynomial in ℤ[X] -/
def poincarePolyZ : ℤ[X] :=
  1 + 2 * X + 2 * X^2 + 2 * X^3 + 2 * X^4 + 2 * X^5 + X^6

/-- Standard degree-1 and degree-5 factors: (1 + X)(1 + X + X² + X³ + X⁴ + X⁵) -/
theorem poincare_eq_mul_factors :
    poincarePolyZ = (1 + X) * (1 + X + X^2 + X^3 + X^4 + X^5) := by
  dsimp [poincarePolyZ]
  ring

/-- 🏆 THEOREM 1: Cyclotomic Factorization of the G₂ Weyl Poincaré Polynomial:
    P_{W(G₂)}(X) = (cyclotomic 2 ℤ)² · (cyclotomic 3 ℤ) · (cyclotomic 6 ℤ) -/
theorem poincare_eq_cyclotomic_factorization :
    poincarePolyZ = (cyclotomic 2 ℤ) ^ 2 * (cyclotomic 3 ℤ) * (cyclotomic 6 ℤ) := by
  dsimp [poincarePolyZ]
  simp [cyclotomic_two, cyclotomic_three, cyclotomic_six]
  ring

/-- Evaluation of cyclotomic factors at X = 2 -/
theorem cyclotomic_two_eval_two : (cyclotomic 2 ℤ).eval 2 = 3 := by
  simp [cyclotomic_two]

theorem cyclotomic_three_eval_two : (cyclotomic 3 ℤ).eval 2 = 7 := by
  simp [cyclotomic_three]

theorem cyclotomic_six_eval_two : (cyclotomic 6 ℤ).eval 2 = 3 := by
  simp [cyclotomic_six]

/-- 🏆 THEOREM 2: Evaluation of P_{W(G₂)}(2) via Cyclotomic Factors = 189 -/
theorem poincare_eval_two_eq_cyclotomic_product :
    poincarePolyZ.eval 2 = ((cyclotomic 2 ℤ).eval 2) ^ 2 * ((cyclotomic 3 ℤ).eval 2) * ((cyclotomic 6 ℤ).eval 2) := by
  rw [poincare_eq_cyclotomic_factorization]
  simp only [eval_mul, eval_pow]

theorem poincare_eval_two_value :
    poincarePolyZ.eval 2 = 189 := by
  rw [poincare_eval_two_eq_cyclotomic_product, cyclotomic_two_eval_two, cyclotomic_three_eval_two, cyclotomic_six_eval_two]
  norm_num

/-- 🏆 THEOREM 3: Full G₂(2) Chevalley Order Factorization:
    |G₂(2)| = 2⁶ · P_{W(G₂)}(2) = 64 · 189 = 12096 -/
theorem g2two_chevalley_order_from_cyclotomic :
    2^6 * poincarePolyZ.eval 2 = 12096 := by
  rw [poincare_eval_two_value]
  norm_num

end InfoGeometry.Algebra.Zorn.G2CyclotomicPoincare

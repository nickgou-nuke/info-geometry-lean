import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2CyclotomicPoincareBridge

/-!
# Abstract Bruhat Weight Summation for the G₂ Weyl Group

This module formalizes only the abstract Weyl-length weight sum:
$$\sum_{w \in W(G_2)} |B w B| = |B| \sum_{w \in W(G_2)} 2^{\ell(w)} = |B| \cdot P_{W(G_2)}(2) = 64 \cdot 189 = 12096.$$

The symbol `bruhatCellSize` is a numerical weight, not the cardinality of a
concrete subset of `SplitOctF2Aut`. No concrete Borel subgroup, Bruhat cell,
coverage theorem, or uniqueness theorem is asserted here.

All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Algebra.Zorn.G2Bruhat

open Polynomial
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2CyclotomicPoincare

/-- The abstract Weyl-length weight attached to an element of W(G₂). -/
def bruhatCellSize (cardB : ℕ) (w : DihedralGroup 6) : ℕ :=
  cardB * (2 ^ (coxeterLength w))

/-- 🏆 THEOREM 1: The sum of all 12 Bruhat cell sizes with |B| = 64 is exactly 12096. -/
theorem weighted_bruhat_sum_eq_12096 :
    (∑ w : DihedralGroup 6, bruhatCellSize 64 w) = 12096 := by
  decide

/-- 🏆 THEOREM 2: The sum of the 12 Bruhat cells matches cardB * eval 2 poincareSum. -/
theorem weighted_bruhat_sum_eq_cardB_mul_eval (cardB : ℕ) :
    (∑ w : DihedralGroup 6, bruhatCellSize cardB w) =
      cardB * (eval 2 poincareSum).toNat := by
  have hP : (eval 2 poincareSum).toNat = 189 := by
    rw [poincareSum_eval_two]
    rfl
  rw [hP]
  dsimp [bruhatCellSize]
  rw [← Finset.mul_sum]
  have hsum : (∑ w : DihedralGroup 6, 2 ^ (coxeterLength w)) = 189 := by
    decide
  rw [hsum]

/-- 🏆 THEOREM 3: The cyclotomic factorization of the Bruhat cell sum. -/
theorem weighted_bruhat_sum_cyclotomic (cardB : ℕ) :
    (∑ w : DihedralGroup 6, bruhatCellSize cardB w) =
      cardB * (eval 2 ((cyclotomic 2 ℤ)^2 * cyclotomic 3 ℤ * cyclotomic 6 ℤ)).toNat := by
  rw [weighted_bruhat_sum_eq_cardB_mul_eval]
  have hfact := poincareSum_cyclotomic_factorization
  rw [← hfact]

end InfoGeometry.Algebra.Zorn.G2Bruhat

import Mathlib.Algebra.Polynomial.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

open Polynomial
open DihedralGroup

/-!
# Cyclotomic Factorization of the G₂ Poincaré Polynomial and Bruhat Enumerator

This file formalizes the algebraic Poincaré polynomial of the type-$G_2$ Weyl group:
$$P_{W(G_2)}(X) = \sum_{w \in W(G_2)} X^{\ell(w)} = (1 + X)(1 + X + X^2 + X^3 + X^4 + X^5)$$
and proves its cyclotomic factorization:
$$P_{W(G_2)}(X) = \Phi_2(X)^2 \cdot \Phi_3(X) \cdot \Phi_6(X).$$

Specializing at $X = 2$ (the field order $|\mathbb{F}_2| = 2$) gives:
$$P_{W(G_2)}(2) = \Phi_2(2)^2 \cdot \Phi_3(2) \cdot \Phi_6(2) = 3^2 \cdot 7 \cdot 3 = 189.$$

The final arithmetic theorem below is only an abstract weighted identity.  It
does not identify a concrete Borel subgroup or the carrier
`SplitOctF2Aut` with a Bruhat union.
-/

namespace InfoGeometry.Algebra.Zorn.G2CyclotomicPoincare

/-- The standard Coxeter length of the 12 elements of W(G₂) ≅ DihedralGroup 6. -/
def coxeterLength : DihedralGroup 6 → ℕ
  | r 0 => 0
  | r 1 => 2
  | r 2 => 4
  | r 3 => 6
  | r 4 => 4
  | r 5 => 2
  | sr 0 => 1
  | sr 1 => 1
  | sr 2 => 3
  | sr 3 => 3
  | sr 4 => 5
  | sr 5 => 5

/-- The Poincaré polynomial / Coxeter length enumerator of W(G₂). -/
noncomputable def poincareSum : ℤ[X] :=
  ∑ w : DihedralGroup 6, X ^ (coxeterLength w)

/-- 🏆 THEOREM 1: The explicit polynomial expansion of the Poincaré sum:
    ∑ w ∈ W(G₂), X^{\ell(w)} = 1 + 2X + 2X² + 2X³ + 2X⁴ + 2X⁵ + X⁶. -/
theorem poincareSum_eq_poly :
    poincareSum = 1 + 2*X + 2*X^2 + 2*X^3 + 2*X^4 + 2*X^5 + X^6 := by
  unfold poincareSum
  have huniv : (Finset.univ : Finset (DihedralGroup 6)) =
      {r 0, r 1, r 2, r 3, r 4, r 5, sr 0, sr 1, sr 2, sr 3, sr 4, sr 5} := by
    decide
  rw [huniv]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have hr0 : coxeterLength (r 0) = 0 := rfl
  have hr1 : coxeterLength (r 1) = 2 := rfl
  have hr2 : coxeterLength (r 2) = 4 := rfl
  have hr3 : coxeterLength (r 3) = 6 := rfl
  have hr4 : coxeterLength (r 4) = 4 := rfl
  have hr5 : coxeterLength (r 5) = 2 := rfl
  have hsr0 : coxeterLength (sr 0) = 1 := rfl
  have hsr1 : coxeterLength (sr 1) = 1 := rfl
  have hsr2 : coxeterLength (sr 2) = 3 := rfl
  have hsr3 : coxeterLength (sr 3) = 3 := rfl
  have hsr4 : coxeterLength (sr 4) = 5 := rfl
  have hsr5 : coxeterLength (sr 5) = 5 := rfl
  rw [hr0, hr1, hr2, hr3, hr4, hr5, hsr0, hsr1, hsr2, hsr3, hsr4, hsr5]
  ring

/-- 🏆 THEOREM 2: The canonical product factorization of the Poincaré sum:
    P(X) = (1 + X)(1 + X + X² + X³ + X⁴ + X⁵). -/
theorem poincareSum_factorization :
    poincareSum = (1 + X) * (1 + X + X^2 + X^3 + X^4 + X^5) := by
  rw [poincareSum_eq_poly]
  ring

/-- 🏆 THEOREM 3: The genuine cyclotomic factorization over ℤ[X]:
    P(X) = Φ₂(X)² · Φ₃(X) · Φ₆(X). -/
theorem poincareSum_cyclotomic_factorization :
    poincareSum = (cyclotomic 2 ℤ)^2 * cyclotomic 3 ℤ * cyclotomic 6 ℤ := by
  rw [poincareSum_eq_poly]
  rw [cyclotomic_two, cyclotomic_three, cyclotomic_six]
  ring

/-- 🏆 THEOREM 4: Evaluation at X = 2 (the F₂ ground field):
    P(2) = Φ₂(2)² · Φ₃(2) · Φ₆(2) = 3² · 7 · 3 = 189. -/
theorem poincareSum_eval_two :
    eval (2 : ℤ) poincareSum = 189 := by
  rw [poincareSum_factorization]
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_one]
  norm_num

/-- THEOREM 5: Abstract Borel-weighted Poincaré arithmetic.  This is not a
    cardinality theorem for `SplitOctF2Aut`; a concrete Bruhat partition is
    required before that interpretation is available. -/
theorem abstract_borel_weighted_poincare (cardB : ℕ) (hB : cardB = 64) :
    cardB * (eval (2 : ℤ) poincareSum).toNat = 12096 := by
  rw [hB, poincareSum_eval_two]
  rfl

end InfoGeometry.Algebra.Zorn.G2CyclotomicPoincare

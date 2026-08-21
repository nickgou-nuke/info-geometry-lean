import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Combinatorial Poincaré Polynomial and Chevalley Order Arithmetic of G₂

This module provides the pure combinatorial and polynomial arithmetic of the
abstract $G_2$ root system and dihedral Weyl group $W(G_2) \cong D_{12}$.

## Mathematical Truth & Scope:
- **Scope**: Combinatorial length distribution of the Coxeter group $W(G_2)$,
  the Poincaré polynomial $P_W(q) = \sum_{w \in W} q^{\ell(w)}$, and its evaluation
  at $q = 2$.
- **Boundary**: This module is purely polynomial and combinatorial arithmetic.
  It does **NOT** construct the Bruhat cells of the concrete automorphism carrier
  `SplitOctF2Aut`, nor does it claim to derive the carrier cardinality $| \operatorname{Aut}(\mathbb{O}_s(\mathbb{F}_2)) | = 12096$.
  That classification remains open closure debt in the concrete algebra DAG.

All theorems here are kernel-checked algebraic/combinatorial identities with 0 `sorry`s.
-/

open Finset

namespace InfoGeometry.Algebra.Zorn.G2Combinatorics

/-! ### 1. Abstract Positive Root Set and Card -/

/-- The 6 positive roots of the abstract G₂ root system -/
inductive G2PositiveRoot : Type
  | alpha                -- simple short root α
  | beta                 -- simple long root β
  | alpha_add_beta       -- α + β (short)
  | two_alpha_beta       -- 2α + β (short)
  | three_alpha_beta     -- 3α + β (long)
  | three_alpha_two_beta -- 3α + 2β (long, highest root)
  deriving DecidableEq, Fintype

/-- Height of each positive root -/
def rootHeight : G2PositiveRoot → ℕ
  | .alpha => 1
  | .beta => 1
  | .alpha_add_beta => 2
  | .two_alpha_beta => 3
  | .three_alpha_beta => 4
  | .three_alpha_two_beta => 5

/-- Theorem: The abstract root system has exactly 6 positive roots. -/
theorem positive_roots_card : Fintype.card G2PositiveRoot = 6 := by
  decide

/-- Formal unipotent group order polynomial: q^|Φ⁺| = q⁶ -/
def formalUnipotentOrder (q : ℕ) : ℕ := q ^ (Fintype.card G2PositiveRoot)

theorem formalUnipotentOrder_two : formalUnipotentOrder 2 = 64 := by
  dsimp [formalUnipotentOrder, positive_roots_card]

/-- Formal Borel subgroup order polynomial: q⁶ (q - 1)² -/
def formalBorelOrder (q : ℕ) : ℕ := (formalUnipotentOrder q) * ((q - 1) ^ 2)

theorem formalBorelOrder_two : formalBorelOrder 2 = 64 := by
  dsimp [formalBorelOrder, formalUnipotentOrder]
  decide

/-! ### 2. The Dihedral Weyl Group W(G₂) Length Distribution -/

/-- The 12 elements of the dihedral Coxeter group W(G₂) ≅ D₁₂ -/
inductive G2WeylElement : Type
  | id
  | s1
  | s2
  | s1s2
  | s2s1
  | s1s2s1
  | s2s1s2
  | s1s2s1s2
  | s2s1s2s1
  | s1s2s1s2s1
  | s2s1s2s1s2
  | w0
  deriving DecidableEq, Fintype

/-- Theorem: The Weyl group W(G₂) has order 12. -/
theorem weyl_group_card : Fintype.card G2WeylElement = 12 := by
  decide

/-- Coxeter length of each Weyl element -/
def weylLength : G2WeylElement → ℕ
  | .id => 0
  | .s1 => 1
  | .s2 => 1
  | .s1s2 => 2
  | .s2s1 => 2
  | .s1s2s1 => 3
  | .s2s1s2 => 3
  | .s1s2s1s2 => 4
  | .s2s1s2s1 => 4
  | .s1s2s1s2s1 => 5
  | .s2s1s2s1s2 => 5
  | .w0 => 6

/-- The Poincaré polynomial P_W(q) = ∑_{w ∈ W} q^{ℓ(w)} -/
def poincarePolynomial (q : ℕ) : ℕ :=
  ∑ w : G2WeylElement, q ^ (weylLength w)

/-- Theorem: The Poincaré polynomial of W(G₂) evaluated at q = 2 equals 189. -/
theorem poincare_polynomial_at_two : poincarePolynomial 2 = 189 := by
  dsimp [poincarePolynomial, weylLength]
  decide

/-! ### 3. Polynomial Chevalley Order Formula -/

/-- Formal Bruhat cell polynomial sum: P_Bruhat(q) = |B(q)| · P_W(q) = q⁶(q-1)² · ∑ q^{ℓ(w)} -/
def formalBruhatOrder (q : ℕ) : ℕ :=
  (formalBorelOrder q) * (poincarePolynomial q)

/-- 
  Theorem: The formal Bruhat polynomial at q = 2 evaluates to 12,096:
  P_Bruhat(2) = 64 · 189 = 12,096.
-/
theorem formal_bruhat_order_at_two :
    formalBruhatOrder 2 = 12096 := by
  dsimp [formalBruhatOrder]
  rw [formalBorelOrder_two, poincare_polynomial_at_two]

/-- Standard Lie-theoretic product formula: |G₂(q)| = q⁶ (q² - 1) (q⁶ - 1) -/
def lieAlgebraG2OrderFormula (q : ℕ) : ℕ :=
  q^6 * (q^2 - 1) * (q^6 - 1)

/-- Theorem: The Lie-theoretic product formula at q = 2 evaluates to 12,096. -/
theorem lie_algebra_g2_formula_at_two :
    lieAlgebraG2OrderFormula 2 = 12096 := by
  dsimp [lieAlgebraG2OrderFormula]

/-- Theorem: Combinatorial agreement between Bruhat polynomial sum and Lie order formula. -/
theorem bruhat_sum_eq_chevalley_formula :
    formalBruhatOrder 2 = lieAlgebraG2OrderFormula 2 := by
  rw [formal_bruhat_order_at_two, lie_algebra_g2_formula_at_two]

end InfoGeometry.Algebra.Zorn.G2Combinatorics

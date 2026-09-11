import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Noncommutative Poisson Structure, Lie Homomorphisms, and Noether Conservation

This module formalizes:
1. The Noncommutative Commutator Bracket `[X, Y] = X Y - Y X`.
2. Skew-Symmetry and the Noncommutative Jacobi Identity.
3. The Inner Derivation `ad_X : A →ₗ[R] A` and its Leibniz product rule.
4. The Lie Homomorphism of Inner Derivations: `[ad_X, ad_Y](Z) = ad_{[X, Y]}(Z)`.
5. Noncommutative Noether Theorem: `[H, Q] = 0 ⟹ ad_H(Q) = 0`.
6. Gauge and Outer Derivation Invariance of Conserved Brackets.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.NCG

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-- The noncommutative commutator bracket [X, Y] = X * Y - Y * X -/
def bracket (X Y : A) : A :=
  X * Y - Y * X

theorem bracket_apply (X Y : A) : bracket X Y = X * Y - Y * X := by
  dsimp [bracket]

/-- 🏆 THEOREM 1: Skew-Symmetry of the Noncommutative Bracket:
    [X, Y] = - [Y, X] -/
theorem bracket_skew (X Y : A) :
    bracket X Y = - bracket Y X := by
  dsimp [bracket]
  abel

/-- Vanishing of the commutator bracket is exactly multiplicative
commutation in the ambient ring. -/
theorem bracket_eq_zero_iff (X Y : A) :
    bracket X Y = 0 ↔ X * Y = Y * X := by
  simp [bracket, sub_eq_zero]

@[simp]
theorem bracket_add_left (X Y Z : A) :
    bracket (X + Y) Z = bracket X Z + bracket Y Z := by
  simp only [bracket, add_mul, mul_add]
  abel

@[simp]
theorem bracket_add_right (X Y Z : A) :
    bracket X (Y + Z) = bracket X Y + bracket X Z := by
  simp only [bracket, add_mul, mul_add]
  abel

theorem bracket_smul_left (r : R) (X Y : A) :
    bracket (r • X) Y = r • bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem bracket_smul_right (r : R) (X Y : A) :
    bracket X (r • Y) = r • bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- 🏆 THEOREM 2: The Noncommutative Jacobi Identity:
    [X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] = 0 -/
theorem bracket_jacobi (X Y Z : A) :
    bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0 := by
  dsimp [bracket]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- The Inner Derivation ad_X : A →ₗ[R] A given by ad_X(Y) = [X, Y] -/
def adLie (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A] (X : A) : A →ₗ[R] A where
  toFun Y := bracket X Y
  map_add' Y Z := by
    dsimp [bracket]
    simp only [mul_add, add_mul]
    abel
  map_smul' r Y := by
    dsimp [bracket]
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem adLie_apply (X Y : A) : adLie R X Y = X * Y - Y * X := by
  dsimp [adLie, bracket]

/-- 🏆 THEOREM 3: The Inner Derivation satisfies the Leibniz Rule:
    ad_X(Y * Z) = ad_X(Y) * Z + Y * ad_X(Z) -/
theorem adLie_leibniz (X Y Z : A) :
    adLie R X (Y * Z) = adLie R X Y * Z + Y * adLie R X Z := by
  dsimp [adLie, bracket]
  calc
    X * (Y * Z) - (Y * Z) * X
      = (X * Y * Z - Y * X * Z) + (Y * X * Z - Y * Z * X) := by
        simp only [mul_assoc]
        abel
    _ = (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by
        simp only [sub_mul, mul_sub, mul_assoc]

/-- 🏆 THEOREM 4: Lie Homomorphism of Inner Derivations:
    [ad_X, ad_Y](Z) = ad_[X, Y](Z) -/
theorem adLie_commutator (X Y Z : A) :
    adLie R X (adLie R Y Z) - adLie R Y (adLie R X Z) = adLie R (bracket X Y) Z := by
  dsimp [adLie, bracket]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- 🏆 THEOREM 5: Noncommutative Noether Conservation Law:
    If a charge Q commutes with the Hamiltonian H ([H, Q] = 0),
    then the infinitesimal evolution of Q vanishes: ad_H(Q) = 0. -/
theorem noncommutative_noether (H Q : A) (h_comm : bracket H Q = 0) :
    adLie R H Q = 0 := by
  dsimp [adLie]
  exact h_comm

/-- 🏆 THEOREM 6: Preservation of Conserved Quantities under Algebra Derivations:
    If an outer derivation D leaves H and Q invariant (D(H) = 0 and D(Q) = 0),
    then D also annihilates their bracket: D([H, Q]) = 0. -/
theorem derivation_bracket_invariant
    (D : A →ₗ[R] A)
    (hD_leibniz : ∀ x y, D (x * y) = D x * y + x * D y)
    (H Q : A) (hH : D H = 0) (hQ : D Q = 0) :
    D (bracket H Q) = 0 := by
  dsimp [bracket]
  rw [D.map_sub, hD_leibniz, hD_leibniz, hH, hQ]
  simp only [zero_mul, mul_zero, add_zero, sub_self]

/- Every Leibniz derivation transports the commutator bracket by the
   corresponding Leibniz rule. -/
theorem derivation_bracket_leibniz
    (D : A →ₗ[R] A)
    (hD_leibniz : ∀ x y, D (x * y) = D x * y + x * D y)
    (X Y : A) :
    D (bracket X Y) = bracket (D X) Y + bracket X (D Y) := by
  dsimp [bracket]
  rw [D.map_sub, hD_leibniz, hD_leibniz]
  abel

end InfoGeometry.NCG

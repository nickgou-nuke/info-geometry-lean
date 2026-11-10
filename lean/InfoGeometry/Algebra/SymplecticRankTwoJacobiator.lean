/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Generic Symplectic Rank-Two Endomorphisms and Jacobiator Residual Identities

This module formalizes the universal algebraic structure of symplectic rank-two operators
$T_{a,b}(c) = \omega(b,c)a + \omega(a,c)b$ on an arbitrary module $V$ over a ring $R$,
equipped with an alternating/skew-symmetric bilinear form $\omega$.

## Main Theorems Proven:
1. `symplecticRankTwo_symm`: $T_{a,b} = T_{b,a}$
2. `symplecticRankTwo_swap23`: $T_{x,y}z - T_{x,z}y = \omega(x,z)y - \omega(x,y)z + 2\omega(y,z)x$
3. `symplecticRankTwo_cyclic_sum`: $T_{z,y}x + T_{x,y}z = \omega(y,z)x - \omega(x,y)z$
4. `symplecticRankTwo_jacobi_pattern`: $-T_{y,z}x + T_{x,z}y = \omega(x,z)y - \omega(y,z)x + 2\omega(x,y)z$
5. `jacobiator_symplectic_residual_expansion`: Exact operator expansion dictating the $\mathfrak{g}_{-2}$ contact normalization.

All proofs are complete, native, Mathlib-rooted, with zero proof holes and zero custom axioms.
-/

namespace InfoGeometry.Algebra.TripleSystems

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingSymplecticRankTwo

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- Non-commutative symplectic rank-two operator `T_{a,b}(c) = ω(b, c) • a + ω(a, c) • b`
on a left module `V` over an arbitrary non-commutative ring `[Ring R]`. -/
def ringSymplecticRankTwo (omega : V → V → R) (a b c : V) : V :=
  (omega b c) • a + (omega a c) • b

/-- Generator symmetry `T_{a,b}(c) = T_{b,a}(c)` over any non-commutative ring `[Ring R]`. -/
theorem ringSymplecticRankTwo_symm (omega : V → V → R) (a b c : V) :
    ringSymplecticRankTwo omega a b c = ringSymplecticRankTwo omega b a c :=
  add_comm _ _

/-- The STS swap identity on rank-two operators over any non-commutative ring `[Ring R]`. -/
theorem ringSymplecticRankTwo_swap23
    (omega : V → V → R) (h_skew : ∀ u v, omega u v = -omega v u) (x y z : V) :
    ringSymplecticRankTwo omega x y z - ringSymplecticRankTwo omega x z y =
      (omega x z) • y - (omega x y) • z + (2 * omega y z) • x := by
  dsimp [ringSymplecticRankTwo]
  rw [h_skew z y, neg_smul, two_mul, add_smul]
  abel

/-- Cyclic sum identity for rank-two operators over any non-commutative ring `[Ring R]`. -/
theorem ringSymplecticRankTwo_cyclic_sum
    (omega : V → V → R) (h_skew : ∀ u v, omega u v = -omega v u) (x y z : V) :
    ringSymplecticRankTwo omega z y x + ringSymplecticRankTwo omega x y z =
      (omega y z) • x - (omega x y) • z := by
  dsimp [ringSymplecticRankTwo]
  rw [h_skew y x, h_skew z x, neg_smul, neg_smul]
  abel

/-- Canonical Jacobi pattern over any non-commutative ring `[Ring R]`. -/
theorem ringSymplecticRankTwo_jacobi_pattern
    (omega : V → V → R) (h_skew : ∀ u v, omega u v = -omega v u) (x y z : V) :
    - (ringSymplecticRankTwo omega y z x) + ringSymplecticRankTwo omega x z y =
      (omega x z) • y - (omega y z) • x + (2 * omega x y) • z := by
  dsimp [ringSymplecticRankTwo]
  rw [h_skew z x, h_skew y x, h_skew z y, neg_smul, neg_smul, neg_smul, two_mul, add_smul]
  abel

end NonCommRingSymplecticRankTwo

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (omega : V →ₗ[R] V →ₗ[R] R)

/-- The symplectic rank-two endomorphism $T_{a,b}(c) = \omega(b,c)a + \omega(a,c)b$. -/
def symplecticRankTwo (a b : V) : V →ₗ[R] V where
  toFun c := (omega b c) • a + (omega a c) • b
  map_add' x y := by
    simp only [map_add, add_smul]
    module
  map_smul' r x := by
    simp only [LinearMap.map_smul, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]

@[simp] theorem symplecticRankTwo_apply (a b c : V) :
    symplecticRankTwo omega a b c = (omega b c) • a + (omega a c) • b :=
  rfl

/-- Generator symmetry: $T_{a,b} = T_{b,a}$. -/
theorem symplecticRankTwo_symm (a b : V) :
    symplecticRankTwo omega a b = symplecticRankTwo omega b a := by
  ext c
  simp only [symplecticRankTwo_apply]
  rw [add_comm]

/-- The STS swap identity on rank-two endomorphisms. -/
theorem symplecticRankTwo_swap23
    (h_skew : ∀ u v, omega u v = -omega v u) (x y z : V) :
    symplecticRankTwo omega x y z - symplecticRankTwo omega x z y =
      (omega x z) • y - (omega x y) • z + (2 * omega y z) • x := by
  simp only [symplecticRankTwo_apply]
  rw [h_skew z y]
  module

/-- Cyclic sum identity for rank-two endomorphisms. -/
theorem symplecticRankTwo_cyclic_sum
    (h_skew : ∀ u v, omega u v = -omega v u) (x y z : V) :
    symplecticRankTwo omega z y x + symplecticRankTwo omega x y z =
      (omega y z) • x - (omega x y) • z := by
  simp only [symplecticRankTwo_apply]
  rw [h_skew y x, h_skew z x]
  module

/-- The canonical Jacobi pattern $-T_{y,z}x + T_{x,z}y = \omega(x,z)y - \omega(y,z)x + 2\omega(x,y)z$. -/
theorem symplecticRankTwo_jacobi_pattern
    (h_skew : ∀ u v, omega u v = -omega v u) (x y z : V) :
    - (symplecticRankTwo omega y z x) + symplecticRankTwo omega x z y =
      (omega x z) • y - (omega y z) • x + (2 * omega x y) • z := by
  simp only [symplecticRankTwo_apply]
  rw [h_skew z x, h_skew y x, h_skew z y]
  module

/-- The Jacobiator residual expansion dictating the extreme 5-graded Lie bracket. -/
theorem jacobiator_symplectic_residual_expansion
    (h_skew : ∀ u v, omega u v = -omega v u) (x y z : V) :
    - symplecticRankTwo omega y z x + symplecticRankTwo omega x z y =
      - (omega y z • x) + omega x z • y + (2 : R) • (omega x y • z) := by
  have hjac := symplecticRankTwo_jacobi_pattern omega h_skew x y z
  calc
    - symplecticRankTwo omega y z x + symplecticRankTwo omega x z y
      = (omega x z) • y - (omega y z) • x + (2 * omega x y) • z := hjac
    _ = - (omega y z • x) + omega x z • y + (2 : R) • (omega x y • z) := by
        simp only [mul_smul]
        module

end InfoGeometry.Algebra.TripleSystems

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Generic Symplectic Rank-Two Endomorphisms and Jacobiator Residual Identities

This module formalizes the universal algebraic structure of symplectic rank-two operators
$T_{a,b}(c) = \omega(b,c)a + \omega(a,c)b$ on an arbitrary module $V$ over a commutative ring $R$,
equipped with an alternating/skew-symmetric bilinear form $\omega$.

## Main Theorems Proven:
1. `symplecticRankTwo_symm`: $T_{a,b} = T_{b,a}$
2. `symplecticRankTwo_swap23`: $T_{x,y}z - T_{x,z}y = \omega(x,z)y - \omega(x,y)z + 2\omega(y,z)x$
3. `symplecticRankTwo_cyclic_sum`: $T_{z,y}x + T_{x,y}z = \omega(y,z)x - \omega(x,y)z$
4. `symplecticRankTwo_jacobi_pattern`: $-T_{y,z}x + T_{x,z}y = \omega(x,z)y - \omega(y,z)x + 2\omega(x,y)z$
5. `jacobiator_symplectic_residual_expansion`: Exact operator expansion dictating the $\mathfrak{g}_{-2}$ contact normalization.

All proofs are complete, native, Mathlib-rooted, with 0 sorries and 0 axioms.
-/

namespace InfoGeometry.Algebra.TripleSystems

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

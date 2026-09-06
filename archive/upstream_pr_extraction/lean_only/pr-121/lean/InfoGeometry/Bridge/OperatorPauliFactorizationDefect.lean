import Mathlib.Tactic
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

/-!
# Noncommutative Pauli factorization defect

The ordinary Pauli soldering identity becomes scalar only when its coordinate
coefficients commute.  This file records the exact algebraic obstruction on an
arbitrary associative ring, directly in the chiral coordinates

`(t, z, u, v) = (X^0, X^3, X^right, X^left)`.

No geometric curvature, connection, or Lichnerowicz formula is inferred from
these finite ring identities.  Such an interpretation requires a separate
differential-geometric owner.
-/

namespace InfoGeometry.Bridge.OperatorPauliFactorizationDefect

open Matrix
open scoped Matrix

abbrev OperatorBlock (A : Type*) := Matrix (Fin 2) (Fin 2) A

/-- The additive commutator in an associative ring. -/
def commutator {A : Type*} [Ring A] (x y : A) : A :=
  x * y - y * x

/-- Pauli paravector written in null/circular coordinates. -/
def operatorSigma {A : Type*} [Ring A] (t z u v : A) :
    OperatorBlock A :=
  !![t + z, u; v, t - z]

/-- Metric-conjugate Pauli paravector. -/
def operatorBarSigma {A : Type*} [Ring A] (t z u v : A) :
    OperatorBlock A :=
  !![t - z, -u; -v, t + z]

/-- The ordered quadratic expression used as the scalar candidate. -/
def orderedQuadratic {A : Type*} [Ring A] (t z u v : A) : A :=
  t * t - z * z - u * v

/-- Diagonal embedding of a scalar candidate into the Pauli block. -/
def diagonalBlock {A : Type*} [Ring A] (q : A) : OperatorBlock A :=
  !![q, 0; 0, q]

/-- Exact expansion of the forward Pauli product.  The off-diagonal entries
are pure commutator defects; the two diagonal orderings need not agree. -/
theorem operatorSigma_mul_operatorBarSigma
    {A : Type*} [Ring A] (t z u v : A) :
    operatorSigma t z u v * operatorBarSigma t z u v =
      !![
        t * t - z * z + commutator z t - u * v,
        commutator u t + commutator u z;
        commutator v t - commutator v z,
        t * t - z * z + commutator t z - v * u
      ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSigma, operatorBarSigma, commutator,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- Exact expansion of the reverse Pauli product. -/
theorem operatorBarSigma_mul_operatorSigma
    {A : Type*} [Ring A] (t z u v : A) :
    operatorBarSigma t z u v * operatorSigma t z u v =
      !![
        t * t - z * z + commutator t z - u * v,
        commutator t u - commutator z u;
        commutator t v + commutator z v,
        t * t - z * z + commutator z t - v * u
      ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSigma, operatorBarSigma, commutator,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- The complete obstruction to the scalar determinant factorization, relative
to the ordering `t^2 - z^2 - uv`. -/
def factorizationDefect {A : Type*} [Ring A] (t z u v : A) :
    OperatorBlock A :=
  !![
    commutator z t,
    commutator u t + commutator u z;
    commutator v t - commutator v z,
    commutator t z + commutator u v
  ]

/-- The operator product is the ordered quadratic diagonal plus the exact
commutator defect. -/
theorem operator_factorization_with_defect
    {A : Type*} [Ring A] (t z u v : A) :
    operatorSigma t z u v * operatorBarSigma t z u v =
      diagonalBlock (orderedQuadratic t z u v) +
        factorizationDefect t z u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSigma, operatorBarSigma, orderedQuadratic, diagonalBlock,
      factorizationDefect, commutator, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- Pairwise commuting chiral coordinates recover the classical scalar
factorization. -/
theorem operator_factorization_of_pairwise_commute
    {A : Type*} [Ring A] (t z u v : A)
    (htz : t * z = z * t)
    (htu : t * u = u * t)
    (htv : t * v = v * t)
    (hzu : z * u = u * z)
    (hzv : z * v = v * z)
    (huv : u * v = v * u) :
    operatorSigma t z u v * operatorBarSigma t z u v =
      diagonalBlock (orderedQuadratic t z u v) := by
  rw [operator_factorization_with_defect]
  have hdefect : factorizationDefect t z u v = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [factorizationDefect, commutator, htz, htu, htv, hzu, hzv, huv]
  rw [hdefect, add_zero]

/-- Under the same commutativity hypotheses, the reverse ordering gives the
same scalar factorization. -/
theorem reverse_operator_factorization_of_pairwise_commute
    {A : Type*} [Ring A] (t z u v : A)
    (htz : t * z = z * t)
    (htu : t * u = u * t)
    (htv : t * v = v * t)
    (hzu : z * u = u * z)
    (hzv : z * v = v * z)
    (huv : u * v = v * u) :
    operatorBarSigma t z u v * operatorSigma t z u v =
      diagonalBlock (orderedQuadratic t z u v) := by
  rw [operatorBarSigma_mul_operatorSigma]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalBlock, orderedQuadratic, commutator,
      htz, htu, htv, hzu, hzv, huv] <;>
    noncomm_ring

end InfoGeometry.Bridge.OperatorPauliFactorizationDefect

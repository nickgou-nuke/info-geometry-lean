import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# InfoGeometry.Canonical.OperatorChiralDeterminantDefect

Exact algebraic obstruction to the classical two-by-two determinant
factorization after the chiral coordinates are lifted to noncommuting
operators.

For a classical commutative block

`X = [[p,r],[l,m]]`

its adjugate is

`X~ = [[m,-r],[-l,p]]`

and `X X~ = det(X) I`.  Over an arbitrary noncommutative ring the same matrix
multiplication instead produces two ordered quadratic readouts on the diagonal
and commutators off the diagonal.  This file records that identity directly;
no determinant on a noncommutative coefficient ring is introduced.

The result is the finite algebraic analogue of the familiar fact that a
first-order Clifford operator can acquire commutator/curvature terms when it
is squared.  The file does not identify those algebraic commutators with a
geometric curvature tensor without additional differential-geometric data.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorChiralDeterminantDefect

open Matrix

universe u

variable {A : Type u} [Ring A]

abbrev ChiralBlock (A : Type u) [Ring A] := Matrix (Fin 2) (Fin 2) A

/-- Chiral/circular two-by-two operator block. -/
def chiralBlock (p m r l : A) : ChiralBlock A :=
  !![p, r; l, m]

/-- Classical adjugate formula, retained purely as a matrix operation over a
possibly noncommutative coefficient ring. -/
def chiralAdjugate (p m r l : A) : ChiralBlock A :=
  !![m, -r; -l, p]

/-- Ordered left quadratic channel `p m - r l`. -/
def leftQuadraticReadout (p m r l : A) : A :=
  p * m - r * l

/-- Ordered right quadratic channel `m p - l r`. -/
def rightQuadraticReadout (p m r l : A) : A :=
  m * p - l * r

/-- Ring commutator. -/
def operatorCommutator (x y : A) : A :=
  x * y - y * x

/-- Scalar diagonal block, used instead of a noncommutative determinant. -/
def scalarChiralBlock (d : A) : ChiralBlock A :=
  !![d, 0; 0, d]

/-- Exact noncommutative replacement of `X adj(X) = det(X) I`.

The diagonal entries are the two possible orderings of the quadratic readout;
the off-diagonal entries are precisely commutators. -/
theorem chiralBlock_mul_adjugate
    (p m r l : A) :
    chiralBlock p m r l * chiralAdjugate p m r l =
      !![leftQuadraticReadout p m r l,
          operatorCommutator r p;
         operatorCommutator l m,
          rightQuadraticReadout p m r l] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralBlock, chiralAdjugate, leftQuadraticReadout,
      rightQuadraticReadout, operatorCommutator,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- The mismatch between the two ordered quadratic channels is itself a
commutator defect. -/
theorem left_sub_right_eq_commutator_defect
    (p m r l : A) :
    leftQuadraticReadout p m r l - rightQuadraticReadout p m r l =
      operatorCommutator p m - operatorCommutator r l := by
  simp [leftQuadraticReadout, rightQuadraticReadout, operatorCommutator]
  noncomm_ring

/-- If the four commutations required by the adjugate calculation hold, the
classical scalar factorization is recovered exactly. -/
theorem chiralBlock_mul_adjugate_eq_scalar_of_commute
    (p m r l : A)
    (hpm : Commute p m)
    (hrl : Commute r l)
    (hrp : Commute r p)
    (hlm : Commute l m) :
    chiralBlock p m r l * chiralAdjugate p m r l =
      scalarChiralBlock (leftQuadraticReadout p m r l) := by
  have hoff₁ : operatorCommutator r p = 0 := by
    exact sub_eq_zero.mpr hrp.eq
  have hoff₂ : operatorCommutator l m = 0 := by
    exact sub_eq_zero.mpr hlm.eq
  have hdiag :
      rightQuadraticReadout p m r l = leftQuadraticReadout p m r l := by
    simp [rightQuadraticReadout, leftQuadraticReadout, hpm.eq.symm, hrl.eq.symm]
  rw [chiralBlock_mul_adjugate]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarChiralBlock, hoff₁, hoff₂, hdiag]

/-- Pairwise commuting chiral coordinates recover the ordinary scalar
adjugate identity. -/
theorem chiralBlock_mul_adjugate_eq_scalar_of_pairwise_commute
    (p m r l : A)
    (h : ∀ x ∈ ({p, m, r, l} : Set A),
      ∀ y ∈ ({p, m, r, l} : Set A), Commute x y) :
    chiralBlock p m r l * chiralAdjugate p m r l =
      scalarChiralBlock (leftQuadraticReadout p m r l) := by
  apply chiralBlock_mul_adjugate_eq_scalar_of_commute p m r l
  · exact h p (by simp) m (by simp)
  · exact h r (by simp) l (by simp)
  · exact h r (by simp) p (by simp)
  · exact h l (by simp) m (by simp)

/-! ## Specialization to the repository-owned associative OperatorZornMatrix -/

section OperatorZorn

open InfoGeometry.Physics
open InfoGeometry.Physics.OperatorZornMatrix

variable [StarRing A]

/-- The adjugate matrix attached to the repository's four-entry associative
operator-Zorn carrier. -/
def operatorZornAdjugateMatrix (M : OperatorZornMatrix A) :
    Matrix (Fin 2) (Fin 2) A :=
  chiralAdjugate M.n_plus_op M.n_minus_op
    M.sigma_plus_op M.sigma_minus_op

/-- Exact readback of the noncommutative adjugate defect on
`OperatorZornMatrix.toMatrix`. -/
theorem operatorZorn_toMatrix_mul_adjugate
    (M : OperatorZornMatrix A) :
    toMatrix M * operatorZornAdjugateMatrix M =
      !![leftQuadraticReadout M.n_plus_op M.n_minus_op
            M.sigma_plus_op M.sigma_minus_op,
          operatorCommutator M.sigma_plus_op M.n_plus_op;
         operatorCommutator M.sigma_minus_op M.n_minus_op,
          rightQuadraticReadout M.n_plus_op M.n_minus_op
            M.sigma_plus_op M.sigma_minus_op] := by
  simpa [toMatrix, operatorZornAdjugateMatrix, chiralBlock] using
    (chiralBlock_mul_adjugate
      M.n_plus_op M.n_minus_op M.sigma_plus_op M.sigma_minus_op)

/-- The repository operator-Zorn carrier regains the classical scalar channel
under the corresponding commutativity assumptions. -/
theorem operatorZorn_scalar_factorization_of_commute
    (M : OperatorZornMatrix A)
    (hpm : Commute M.n_plus_op M.n_minus_op)
    (hrl : Commute M.sigma_plus_op M.sigma_minus_op)
    (hrp : Commute M.sigma_plus_op M.n_plus_op)
    (hlm : Commute M.sigma_minus_op M.n_minus_op) :
    toMatrix M * operatorZornAdjugateMatrix M =
      scalarChiralBlock
        (leftQuadraticReadout M.n_plus_op M.n_minus_op
          M.sigma_plus_op M.sigma_minus_op) := by
  simpa [toMatrix, operatorZornAdjugateMatrix, chiralBlock] using
    (chiralBlock_mul_adjugate_eq_scalar_of_commute
      M.n_plus_op M.n_minus_op M.sigma_plus_op M.sigma_minus_op
      hpm hrl hrp hlm)

end OperatorZorn

end InfoGeometry.Canonical.OperatorChiralDeterminantDefect

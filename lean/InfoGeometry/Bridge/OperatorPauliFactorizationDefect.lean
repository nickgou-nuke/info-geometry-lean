import Mathlib.Tactic

/-! Exact noncommutative obstruction to Pauli scalar factorization. -/

namespace InfoGeometry.Bridge.OperatorPauliFactorizationDefect

open Matrix
open scoped Matrix

abbrev OperatorBlock (A : Type*) := Matrix (Fin 2) (Fin 2) A

def commutator {A : Type*} [Ring A] (x y : A) : A := x * y - y * x

def operatorSigma {A : Type*} [Ring A] (t z u v : A) : OperatorBlock A :=
  !![t + z, u; v, t - z]

def operatorBarSigma {A : Type*} [Ring A] (t z u v : A) : OperatorBlock A :=
  !![t - z, -u; -v, t + z]

def orderedQuadratic {A : Type*} [Ring A] (t z u v : A) : A :=
  t * t - z * z - u * v

def diagonalBlock {A : Type*} [Ring A] (q : A) : OperatorBlock A := !![q, 0; 0, q]

theorem operatorSigma_mul_operatorBarSigma
    {A : Type*} [Ring A] (t z u v : A) :
    operatorSigma t z u v * operatorBarSigma t z u v =
      !![t*t-z*z+commutator z t-u*v, commutator u t+commutator u z;
         commutator v t-commutator v z, t*t-z*z+commutator t z-v*u] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSigma, operatorBarSigma, commutator,
      Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

theorem operatorBarSigma_mul_operatorSigma
    {A : Type*} [Ring A] (t z u v : A) :
    operatorBarSigma t z u v * operatorSigma t z u v =
      !![t*t-z*z+commutator t z-u*v, commutator t u-commutator z u;
         commutator t v+commutator z v, t*t-z*z+commutator z t-v*u] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSigma, operatorBarSigma, commutator,
      Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

def factorizationDefect {A : Type*} [Ring A] (t z u v : A) : OperatorBlock A :=
  !![commutator z t, commutator u t + commutator u z;
     commutator v t - commutator v z, commutator t z + commutator u v]

theorem operator_factorization_with_defect
    {A : Type*} [Ring A] (t z u v : A) :
    operatorSigma t z u v * operatorBarSigma t z u v =
      diagonalBlock (orderedQuadratic t z u v) + factorizationDefect t z u v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSigma, operatorBarSigma, orderedQuadratic, diagonalBlock,
      factorizationDefect, commutator, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

theorem operator_factorization_of_pairwise_commute
    {A : Type*} [Ring A] (t z u v : A)
    (htz : t*z = z*t) (htu : t*u = u*t) (htv : t*v = v*t)
    (hzu : z*u = u*z) (hzv : z*v = v*z) (huv : u*v = v*u) :
    operatorSigma t z u v * operatorBarSigma t z u v =
      diagonalBlock (orderedQuadratic t z u v) := by
  rw [operator_factorization_with_defect]
  have h : factorizationDefect t z u v = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [factorizationDefect, commutator, htz, htu, htv, hzu, hzv, huv]
  rw [h, add_zero]

end InfoGeometry.Bridge.OperatorPauliFactorizationDefect

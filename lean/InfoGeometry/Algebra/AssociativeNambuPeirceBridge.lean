/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeZornNambuAssociator
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryComposition
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Associative alternation, cyclic spin relations, and square-zero corners

The existing `NoncommutativeZornNambu.nambu` is the six-term associative
alternator. Its two transpositions and its contraction under cyclic
commutator relations are independent of any Filippov fundamental identity.
The latter identity is not asserted here.

Directed Peirce corners already have zero pairwise products. The same
property holds on the native range of the existing sandwich endomorphism
`sandwichOp R N N` when `N * N = 0`. It need not hold on the right ideal
`N * A`, as the final real-matrix trace counterexample shows.

Left multiplication by a commutator is already the native regular
right-module endomorphism `LinearMap.mulLeft Aᵐᵒᵖ (a * b - b * a)`.
The distinct inner action is the existing `lieOp R (a * b - b * a)`;
its ordered Leibniz theorem `lieOp_mul` is in `PeirceBoundaryDynamics`.
Neither operator is identified with the three-slot alternator, and no
spinor bilinear form or isotropy theorem is supplied implicitly.
-/

namespace InfoGeometry.Algebra.NoncommutativeZornNambu

open InfoGeometry.Core.PeirceDecomposition

variable {A : Type*} [Ring A]

/-- Swapping the first two inputs reverses the associative alternator. -/
theorem nambu_swap_first_two (a b c : A) :
    nambu ⟨b, a, c⟩ = -nambu ⟨a, b, c⟩ := by
  simp only [nambu_eq_alternating_cubic]
  abel

/-- Swapping the last two inputs reverses the associative alternator. -/
theorem nambu_swap_last_two (a b c : A) :
    nambu ⟨a, c, b⟩ = -nambu ⟨a, b, c⟩ := by
  simp only [nambu_eq_alternating_cubic]
  abel

/-- Cyclic commutator relations turn the cubic into the quadratic Casimir
expression. A representation and its scalar Casimir value are separate data. -/
theorem nambu_eq_sum_squares_of_cyclic_comm {a b c : A}
    (hab : comm a b = c) (hbc : comm b c = a) (hca : comm c a = b) :
    nambu ⟨a, b, c⟩ = a * a + b * b + c * c := by
  rw [nambu_eq_cyclic_commutator]
  change a * comm b c + b * comm c a + c * comm a b = _
  rw [hbc, hca, hab]

/-- The existing directed Peirce corner kills the associative alternator,
using its owned zero-product routing law for each ordered pair. -/
theorem nambu_eq_zero_of_mem_peirce10 {p a b c : A} (hp : p * p = p)
    (ha : a ∈ peirce10 p) (hb : b ∈ peirce10 p) (hc : c ∈ peirce10 p) :
    nambu ⟨a, b, c⟩ = 0 := by
  simp only [nambu, dot, cross]
  rw [peirce10_mul_peirce10_eq_zero p hp hb hc,
    peirce10_mul_peirce10_eq_zero p hp hc hb,
    peirce10_mul_peirce10_eq_zero p hp hc ha,
    peirce10_mul_peirce10_eq_zero p hp ha hc,
    peirce10_mul_peirce10_eq_zero p hp ha hb,
    peirce10_mul_peirce10_eq_zero p hp hb ha]
  simp

end InfoGeometry.Algebra.NoncommutativeZornNambu

namespace InfoGeometry.OperatorAlgebra.LieJordan

variable (R : Type*) [Semiring R] {A : Type*} [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The actual native submodule `range (sandwichOp R N N)` has zero
pairwise products when the common sandwich generator is square-zero. -/
theorem mul_eq_zero_of_mem_range_square_zero_sandwich {N x y : A}
    (hN : N * N = 0)
    (hx : x ∈ LinearMap.range (sandwichOp R N N))
    (hy : y ∈ LinearMap.range (sandwichOp R N N)) : x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  change (N * a * N) * (N * b * N) = 0
  calc
    (N * a * N) * (N * b * N) = (N * a) * (N * N) * (b * N) := by
      simp only [mul_assoc]
    _ = 0 := by rw [hN, mul_zero, zero_mul]

end InfoGeometry.OperatorAlgebra.LieJordan

namespace InfoGeometry.Algebra.NoncommutativeZornNambu

/-- A square-zero generator need not give a trace-isotropic right ideal:
`N = E₀₁` and `M = E₁₀` do not commute, while `N*M = E₀₀` has
`trace ((N*M)*(N*M)) = 1`. The pairing here is `trace (X*Y)`. -/
theorem exists_square_zero_right_ideal_trace_nonzero :
    ∃ N M : Matrix (Fin 2) (Fin 2) ℝ,
      N * M ≠ M * N ∧ N * N = 0 ∧
        Matrix.trace ((N * M) * (N * M)) = 1 := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_, ?_, ?_⟩
  · intro h
    have h00 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 0) h
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Algebra.NoncommutativeZornNambu

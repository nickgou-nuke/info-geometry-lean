/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Morita.Matrix

/-!
# Obstruction to representing a trace-visible element as a commutator

The conclusion is conditional on the exact cyclicity law needed by the proof.
No trace on an arbitrary noncommutative ring is assumed to exist.
-/

namespace InfoGeometry.Algebra.CyclicTraceObstruction

variable {A K : Type*} [Ring A] [Ring K]

/-- A cyclic additive functional kills every associative commutator. -/
theorem cyclic_functional_commutator_eq_zero
    (τ : A →+ K)
    (hcyclic : ∀ x y : A, τ (x * y) = τ (y * x))
    (x y : A) :
    τ (x * y - y * x) = 0 := by
  simp only [map_sub, hcyclic x y]
  exact sub_self _

/-- A cyclic additive functional detects an obstruction for every element in
its nonzero locus: such an element cannot be an associative commutator. -/
theorem element_not_commutator_of_cyclic_functional
    (τ : A →+ K)
    (hcyclic : ∀ x y : A, τ (x * y) = τ (y * x))
    (a : A) (ha : τ a ≠ 0) :
    ¬ ∃ x y : A, x * y - y * x = a := by
  rintro ⟨x, y, hcomm⟩
  have hzero := cyclic_functional_commutator_eq_zero τ hcyclic x y
  rw [hcomm] at hzero
  exact ha hzero

/-- The trace induced on an associative homotope by `x ⋆ y := x * w * y`
annihilates its commutators. The order of all factors is retained: its
commutator is `x * w * y - y * w * x`, and the induced functional evaluates
that element after right multiplication by the sandwich element `w`. -/
theorem cyclic_functional_homotope_commutator_eq_zero
    (τ : A →+ K)
    (hcyclic : ∀ x y : A, τ (x * y) = τ (y * x))
    (w x y : A) :
    τ (((x * w * y - y * w * x) * w)) = 0 := by
  have h := cyclic_functional_commutator_eq_zero τ hcyclic (x * w) (y * w)
  simpa only [mul_assoc, sub_mul] using h

/-- The identity is not a commutator in any positive-size real matrix ring.
This is the dimension-uniform cyclic-trace obstruction on the actual
noncommutative matrix algebra. -/
theorem realMatrix_identity_not_commutator {n : ℕ} (hn : 0 < n) :
    ¬ ∃ x y : Matrix (Fin n) (Fin n) ℝ, x * y - y * x = 1 := by
  apply element_not_commutator_of_cyclic_functional
    (Matrix.traceAddMonoidHom (Fin n) ℝ)
    (fun x y => Matrix.trace_mul_comm x y)
    (1 : Matrix (Fin n) (Fin n) ℝ)
  have htrace : Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) = (n : ℝ) := by
    simp [Matrix.trace]
  change Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0
  rw [htrace]
  exact_mod_cast (Nat.ne_of_gt hn)

/-- Apply a coefficient-valued additive functional to the ordinary matrix
trace. The entries may lie in a genuinely noncommutative ring. -/
def matrixCyclicFunctional {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : A →+ K) : Matrix ι ι A →+ K :=
  τ.comp (Matrix.traceAddMonoidHom ι A)

/-- A cyclic coefficient functional induces a cyclic functional on square
matrices over the same noncommutative coefficient ring. The proof expands the
matrix product and swaps the two finite summations; it does not commute any
coefficient factors. -/
theorem matrixCyclicFunctional_mul_cyclic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : A →+ K)
    (hcyclic : ∀ a b : A, τ (a * b) = τ (b * a))
    (X Y : Matrix ι ι A) :
    matrixCyclicFunctional τ (X * Y) = matrixCyclicFunctional τ (Y * X) := by
  simp only [matrixCyclicFunctional, AddMonoidHom.comp_apply,
    Matrix.traceAddMonoidHom_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact hcyclic (X j i) (Y i j)

/-- In a finite matrix ring, the identity cannot be a commutator whenever a
cyclic coefficient functional detects the scalar identity with nonzero
dimension multiple. No commutativity of the matrix entries is assumed. -/
theorem matrix_identity_not_commutator_of_cyclic_functional
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : A →+ K)
    (hcyclic : ∀ a b : A, τ (a * b) = τ (b * a))
    (hunit : τ (Fintype.card ι : A) ≠ 0) :
    ¬ ∃ X Y : Matrix ι ι A, X * Y - Y * X = 1 := by
  apply element_not_commutator_of_cyclic_functional
    (matrixCyclicFunctional τ) (matrixCyclicFunctional_mul_cyclic τ hcyclic)
    (1 : Matrix ι ι A)
  change τ (Matrix.trace (1 : Matrix ι ι A)) ≠ 0
  rw [Matrix.trace_one]
  exact hunit

/-- A nonzero identity in a matrix algebra over the real operator ring
`Matrix (Fin r) (Fin r) ℝ` is not a commutator. The cyclic functional is the
operator trace on each coefficient, while the outer matrix trace is retained
by `matrix_identity_not_commutator_of_cyclic_functional`; no coefficient
commutativity is assumed. -/
theorem operatorMatrix_identity_not_commutator {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) :
    ¬ ∃ X Y : Matrix (Fin n) (Fin n) (Matrix (Fin r) (Fin r) ℝ),
      X * Y - Y * X = 1 := by
  apply matrix_identity_not_commutator_of_cyclic_functional
    (τ := Matrix.traceAddMonoidHom (Fin r) ℝ)
    (fun X Y => Matrix.trace_mul_comm X Y)
  have htrace : Matrix.trace
      ((Fintype.card (Fin n) : Matrix (Fin r) (Fin r) ℝ)) =
        (n : ℝ) * (r : ℝ) := by
    rw [Fintype.card_fin]
    have hcast : (n : Matrix (Fin r) (Fin r) ℝ) =
        (n : ℝ) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
      ext i j
      simp [Matrix.natCast_apply, Matrix.one_apply]
    rw [hcast, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    norm_num
  change Matrix.trace
    ((Fintype.card (Fin n) : Matrix (Fin r) (Fin r) ℝ)) ≠ 0
  rw [htrace]
  exact mul_ne_zero (by exact_mod_cast hn.ne') (by exact_mod_cast hr.ne')

end InfoGeometry.Algebra.CyclicTraceObstruction

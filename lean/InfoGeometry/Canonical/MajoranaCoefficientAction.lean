/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite Majorana coefficient recovery and quadratic action

The coefficient map is Mathlib's finite linear combination. Normalized CAR
make it faithful in a nontrivial real algebra. All statements concern finite
operator spans, not the kernel of a many-body Hamiltonian on a state space.
-/

noncomputable section

namespace InfoGeometry.Canonical.MajoranaCoefficientAction

open InfoGeometry.Canonical.KitaevChainMajoranaZeroModes
open scoped BigOperators

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {N : ℕ} {gamma : Fin (2 * N) → A}

/-- Anticommutation extracts an individual coefficient of a Majorana sum. -/
theorem linearCombination_anticommutator (h : IsMajoranaBasis N gamma)
    (v : Fin (2 * N) → ℝ) (k : Fin (2 * N)) :
    Fintype.linearCombination ℝ gamma v * gamma k +
      gamma k * Fintype.linearCombination ℝ gamma v = (2 * v k) • (1 : A) := by
  calc
    _ = ∑ i, v i • (gamma i * gamma k + gamma k * gamma i) := by
      simp only [Fintype.linearCombination_apply, Finset.sum_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_mul_assoc, mul_smul_comm, smul_add]
    _ = ∑ i, v i • (if i = k then (2 : A) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h i k]
    _ = (2 * v k) • (1 : A) := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp [Algebra.smul_def, mul_comm]
      rw [map_ofNat]

/-- Normalized CAR prevent a nonzero coefficient vector from representing
the zero operator. Nontriviality of the algebra is essential. -/
theorem linearCombination_injective [Nontrivial A] (h : IsMajoranaBasis N gamma) :
    Function.Injective (Fintype.linearCombination ℝ gamma) := by
  intro v w hvw
  funext k
  have heq := congrArg (fun x : A => x * gamma k + gamma k * x) hvw
  rw [linearCombination_anticommutator h, linearCombination_anticommutator h] at heq
  have hs : 2 * v k = 2 * w k := by
    apply (algebraMap ℝ A).injective
    simpa only [Algebra.algebraMap_eq_smul_one] using heq
  linarith

/-- The quadratic monomial acts by the two corresponding CAR contractions. -/
theorem quadratic_monomial_commutator (h : IsMajoranaBasis N gamma)
    (i j k : Fin (2 * N)) :
    (gamma i * gamma j) * gamma k - gamma k * (gamma i * gamma j) =
      (if j = k then (2 : ℝ) • gamma i else 0) -
        (if i = k then (2 : ℝ) • gamma j else 0) := by
  calc
    _ = gamma i * (gamma j * gamma k + gamma k * gamma j) -
        (gamma i * gamma k + gamma k * gamma i) * gamma j := by noncomm_ring
    _ = _ := by
      rw [h j k, h i k]
      split_ifs <;> simp [two_smul, mul_two, two_mul]

/-- Quadratic element with the normalization for the action `K.mulVec`.
No factor of `i` is included; this is the real algebraic commutator action. -/
def quadraticElement (gamma : Fin (2 * N) → A)
    (K : Matrix (Fin (2 * N)) (Fin (2 * N)) ℝ) : A :=
  (1 / 4 : ℝ) • ∑ i, ∑ j, K i j • (gamma i * gamma j)

end InfoGeometry.Canonical.MajoranaCoefficientAction

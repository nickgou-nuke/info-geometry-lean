/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.Algebra.FreedAdditiveCocycle
import InfoGeometry.OperatorAlgebra.FreedGradedCalculus
import InfoGeometry.OperatorAlgebra.FreedDefectChannels

/-!
# Algebraic synthesis of the Freed-inspired source packet

This entry point combines the actual proved dependencies: the odd lift is a
nonunit at a concrete parameter pair, and a cyclic functional turns diagonal
gauge covariance into signed-trace invariance. The coefficient ring remains
arbitrary and noncommutative. These are operator-algebraic results, with the
geometric and field-theoretic scope recorded separately in the task contract.
-/

namespace InfoGeometry.Canonical.FreedOperatorAlgebra

open Matrix InfoGeometry.Algebra.SupermatrixKoszul
open InfoGeometry.Algebra.FreedAdditiveCocycle
open InfoGeometry.OperatorAlgebra.FreedGradedCalculus
open InfoGeometry.OperatorAlgebra.FreedDefectChannels

variable {R : Type*} [Ring R]

/-- The proposed lift family cannot be a representation by invertible matrices. -/
theorem operatorLift_one_one_not_isUnit [Nontrivial R] :
    ¬ IsUnit (operatorLift (1 : R) 1) := walshPlus_not_isUnit

/-- A repeated-pair defect has precisely the coefficient commutator as its
signed diagonal sum. -/
theorem superTrace_repeated_defect (a b : R) :
    superTrace (productDefect a b a b) = a * b - b * a := rfl

section CyclicFunctional

variable {G : Type*} [AddCommGroup G]

/-- Cyclic trace of the repeated-pair defect vanishes without requiring
the coefficient operators themselves to commute. -/
theorem cyclic_superTrace_repeated_defect (tau : R →+ G)
    (hcyc : ∀ a b : R, tau (a * b) = tau (b * a)) (a b : R) :
    tau (superTrace (productDefect a b a b)) = 0 := by
  rw [superTrace_repeated_defect, map_sub, hcyc, sub_self]

/-- Diagonal gauge covariance yields actual invariance after applying a
cyclic additive functional to the coefficient-valued supertrace. -/
theorem cyclic_superTrace_diagonalGauge (tau : R →+ G)
    (hcyc : ∀ a b : R, tau (a * b) = tau (b * a))
    (u v : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    tau (superTrace (diagonalGauge u v * M * diagonalGauge u⁻¹ v⁻¹)) =
      tau (superTrace M) := by
  have hconj (w : Rˣ) (x : R) : tau ((w : R) * x * (↑w⁻¹ : R)) = tau x := by
    rw [hcyc, ← mul_assoc]
    simp
  have hs : superTrace (diagonalGauge u v * M * diagonalGauge u⁻¹ v⁻¹) =
      (u : R) * M 0 0 * (↑u⁻¹ : R) - (v : R) * M 1 1 * (↑v⁻¹ : R) := by
    change (diagonalGauge u v * M * diagonalGauge u⁻¹ v⁻¹) 0 0 -
      (diagonalGauge u v * M * diagonalGauge u⁻¹ v⁻¹) 1 1 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp [diagonalGauge]
  rw [hs, map_sub, hconj, hconj]
  exact (map_sub tau _ _).symm

end CyclicFunctional
end InfoGeometry.Canonical.FreedOperatorAlgebra

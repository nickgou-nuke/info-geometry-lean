/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.BdGChiralBlockMatrix

/-!
# Noncommuting BdG squares and chiral commutators

These identities extend the existing operator-valued block carrier. They
retain the kinetic-pairing commutator and the full operator square.
-/

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A]

/-- The exact square before any kinetic-pairing commutation assumption. -/
theorem massiveBdGHamiltonian_sq_with_commutator (D M : A) :
    massiveBdGHamiltonian D M * massiveBdGHamiltonian D M =
      !![D * D + M * M, D * M - M * D;
         M * D - D * M, D * D + M * M] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massiveBdGHamiltonian, Matrix.mul_apply, Fin.sum_univ_two,
      sub_eq_add_neg, add_comm]

/-- A block-diagonal square is equivalent to vanishing of the actual
kinetic-pairing commutator. -/
theorem massiveBdGHamiltonian_square_diagonal_iff (D M : A) :
    (massiveBdGHamiltonian D M * massiveBdGHamiltonian D M) 0 1 = 0 ↔
      D * M = M * D := by
  rw [massiveBdGHamiltonian_sq_with_commutator]
  simp [sub_eq_zero]

variable [StarRing A]

/-- The chiral acceleration identity retains the complete operator square.
It is an algebraic identity and does not assign a scalar frequency. -/
theorem dirac_chiral_double_commutator (Δ : A) :
    connesDifferential (diracOperator Δ)
        (connesDifferential (diracOperator Δ) chiralGrading) =
      (4 : ℕ) • (diracSquare Δ * chiralGrading) := by
  rw [diracSquare_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesDifferential, diracOperator, chiralGrading]
    <;> noncomm_ring

end InfoGeometry.Physics

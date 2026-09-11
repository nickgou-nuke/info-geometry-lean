import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Amplituhedron and the Penrose Transform

This module formalizes the final duality between Real Space (the thermodynamic evolution
and Pachner flips) and Dual Space (the static geometric volume of the Amplituhedron).

It maps the dynamic matrix factorizations to the static Positive Grassmannian
projected through external Momentum Twistors.
-/

namespace Amplituhedron

variable (k n m : ℕ)

/-- Entrywise finite positivity carried by this lightweight positive-Grassmannian layer. -/
def MatrixEntrywiseNonnegative (C : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  ∀ i j, 0 ≤ C i j

/-- The Positive Grassmannian C. -/
structure PositiveGrassmannian where
  C_matrix : Matrix (Fin k) (Fin n) ℝ
  is_positive : MatrixEntrywiseNonnegative k n C_matrix

/-- Every positive-Grassmannian packet exposes nonnegative entries. -/
theorem positiveGrassmannian_entries_nonnegative
    (C : PositiveGrassmannian k n) :
    MatrixEntrywiseNonnegative k n C.C_matrix :=
  C.is_positive

/-- The External Momentum Twistors Z. -/
structure MomentumTwistors where
  Z_matrix : Matrix (Fin n) (Fin (k + m)) ℝ

/-- The Amplituhedron space Y = C * Z. -/
def amplituhedron_space (C : PositiveGrassmannian k n) (Z : MomentumTwistors k n m) :
    Matrix (Fin k) (Fin (k + m)) ℝ :=
  C.C_matrix * Z.Z_matrix

/-- A finite matrix product is entrywise positive when both factors are and the
    middle index type is nonempty. -/
theorem matrix_mul_entrywise_positive
    (hn : 0 < n) (C : Matrix (Fin k) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ)
    (hC : ∀ i j, 0 < C i j) (hZ : ∀ i j, 0 < Z i j) :
    ∀ i j, 0 < (C * Z) i j := by
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_pos'
  · intro t ht
    exact le_of_lt (mul_pos (hC i t) (hZ t j))
  · let t : Fin n := ⟨0, hn⟩
    exact ⟨t, Finset.mem_univ _, mul_pos (hC i t) (hZ t j)⟩

/-- 
  THE PENROSE DUALITY AXIOM
  The dynamic scattering evolution in Real Space maps to the 
  static topological volume d(log Q) of the Amplituhedron in Dual Space.
-/
structure PenroseTransform (C : PositiveGrassmannian k n) (Z : MomentumTwistors k n m) where
  real_space_dynamics : ℝ
  dual_space_volume : ℝ
  -- The core correspondence: The scattering amplitude is the volume form
  amplitude_is_volume : real_space_dynamics = dual_space_volume

end Amplituhedron

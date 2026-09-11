import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.AssociativityObstruction
import InfoGeometry.Algebra.ZornMatrix

/-!
# Octonion matrix obstruction

Baez's octonion discussion makes one basic point completely precise: a
genuinely nonassociative multiplication cannot be embedded injectively and
multiplicatively into an associative matrix algebra.

This file records that theorem in the split-octonion/Zorn lane by combining the
generic obstruction lemma with the existing native nonassociativity witness for
`ZornVectorMatrix`.
-/

namespace InfoGeometry.Algebra

/-- Ordinary matrix multiplication cannot faithfully represent split-octonion
Zorn multiplication. -/
theorem no_injective_matrix_representation_of_zornMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    {α : Type*} [Semiring α] :
    ¬ ∃ φ : ZornMatrix ℝ → Matrix n n α,
        Function.Injective φ ∧
          (∀ x y : ZornMatrix ℝ, φ (x * y) = φ x * φ y) := by
  intro h
  rcases h with ⟨φ, hinj, hmul⟩
  have hassoc :
      ∀ x y z : ZornMatrix ℝ, (x * y) * z = x * (y * z) :=
    InfoGeometry.Algebra.associative_of_injective_mul_map_to_semigroup
      φ hinj hmul
  exact ZornMatrix.nonassociative_witness
    (hassoc (ZornMatrix.U 0) (ZornMatrix.U 1) (ZornMatrix.U 2))

end InfoGeometry.Algebra

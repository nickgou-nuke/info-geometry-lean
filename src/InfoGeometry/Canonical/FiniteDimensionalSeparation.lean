import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace InfoGeometry.Canonical.FiniteDimensionalSeparation

/-!
Canonical separation lemmas for audit claims that identify a finite-dimensional
carrier with an infinite-dimensional one.  These statements are deliberately
parametric: they do not use coordinates, diagonal matrices, or commutativity
of the ambient algebra.
-/

variable {K V W : Type*} [DivisionRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A linear equivalence transports finite-dimensionality to its codomain. -/
theorem no_linearEquiv_to_infinite_dimensional
    [FiniteDimensional K V] (hW : ¬ FiniteDimensional K W) :
    ¬ Nonempty (V ≃ₗ[K] W) := by
  rintro ⟨e⟩
  exact hW e.finiteDimensional

/-- The contrapositive form, useful when a proposed equivalence is supplied. -/
theorem finiteDimensional_of_linearEquiv
    (e : V ≃ₗ[K] W) [FiniteDimensional K V] :
    FiniteDimensional K W :=
  e.finiteDimensional

/-- Any equivalence notion exposing a linear equivalence is ruled out by an
infinite-dimensional target. -/
theorem no_equiv_with_linear_shadow
    {Iso : Type*} (toLinearEquiv : Iso → V ≃ₗ[K] W)
    [FiniteDimensional K V] (hW : ¬ FiniteDimensional K W) :
    ¬ Nonempty Iso := by
  rintro ⟨e⟩
  exact hW (toLinearEquiv e).finiteDimensional

end InfoGeometry.Canonical.FiniteDimensionalSeparation

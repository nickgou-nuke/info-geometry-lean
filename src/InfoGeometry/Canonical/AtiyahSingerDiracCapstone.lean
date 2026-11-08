import InfoGeometry.IndexTheory.AtiyahSingerDirac

/-!
# Noncommutative Dirac parity and supertrace capstone

This theorem assembles the algebraic operator identities for odd Dirac
operators and cyclic graded traces. Analytic index equality, heat-kernel
asymptotics, and topological characteristic numbers are not part of this
algebraic packet.
-/

namespace InfoGeometry.Canonical.AtiyahSingerDiracCapstone

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
open InfoGeometry.IndexTheory.AtiyahSingerDirac

/-- The Dirac-square parity identity, McKean--Singer cyclic cancellation, and
Peirce supertrace split hold together in an arbitrary associative operator
ring. -/
theorem capstone_operator_supertrace_synthesis {A R : Type*} [Ring A]
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ)
    {γ D X p : A} (hOdd : D * γ + γ * D = 0)
    (hγX : γ * X = X * γ) (hp : p * p = p)
    (hγp : γ * p = p * γ) :
    D * D * γ - γ * (D * D) = 0 ∧
    gradedTrace τ γ (operatorAnticommutator D X) = 0 ∧
    gradedTrace τ γ (oddCorner p X) = 0 ∧
    gradedTrace τ γ (evenCorner p X) = gradedTrace τ γ X := by
  have hγD : γ * D = -(D * γ) := eq_neg_of_add_eq_zero_right hOdd
  exact ⟨dirac_square_grading_commutes hOdd,
    mckean_singer_cyclic_cancellation τ hτ hγD hγX,
    (peirce_supertrace_split τ hτ hp hγp).1,
    (peirce_supertrace_split τ hτ hp hγp).2⟩

end InfoGeometry.Canonical.AtiyahSingerDiracCapstone

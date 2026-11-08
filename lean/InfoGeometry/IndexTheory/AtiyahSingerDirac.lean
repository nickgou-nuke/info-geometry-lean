import InfoGeometry.Canonical.AtiyahSingerDiracSupertraceCapstone

/-!
# Operator-algebraic Dirac parity interface

This module retains the historical import path while exposing only generic
operator identities. It does not model an analytic or topological index by
arithmetic functions.
-/

namespace InfoGeometry.IndexTheory.AtiyahSingerDirac

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace

/-- Oddness of a Dirac operator makes its square even under the grading. -/
theorem dirac_square_grading_commutes {A : Type*} [Ring A]
    {D γ : A} (h_odd : D * γ + γ * D = 0) :
    D * D * γ - γ * (D * D) = 0 :=
  InfoGeometry.Canonical.AtiyahSingerDirac.dirac_sq_grading_commutes h_odd

/-- Cyclic graded-trace cancellation for an odd Dirac operator and an even
operator. -/
theorem mckean_singer_cyclic_cancellation {A R : Type*} [Ring A]
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ)
    {γ D X : A} (hγD : γ * D = -(D * γ))
    (hγX : γ * X = X * γ) :
    gradedTrace τ γ (operatorAnticommutator D X) = 0 :=
  InfoGeometry.Canonical.AtiyahSingerDirac.mckean_singer_algebraic_cancellation
    τ hτ hγD hγX

/-- Cyclic supertrace resolution across even and odd Peirce corners. -/
theorem peirce_supertrace_split {A R : Type*} [Ring A]
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ)
    {γ p X : A} (hp : p * p = p) (hγp : γ * p = p * γ) :
    gradedTrace τ γ (oddCorner p X) = 0 ∧
    gradedTrace τ γ (evenCorner p X) = gradedTrace τ γ X :=
  InfoGeometry.Canonical.AtiyahSingerDirac.graded_trace_peirce_split
    τ hτ hp hγp

end InfoGeometry.IndexTheory.AtiyahSingerDirac

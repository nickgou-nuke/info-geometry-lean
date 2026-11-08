import InfoGeometry.Spectral.Algebra.IteratedPageStabilization
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Explicit convergence contract

The historical convergence owner mixed the incoming degree with the degree of
the exact-couple differential.  This file keeps the convergence theorem honest:
the two eventual vanishing hypotheses are stated directly at the page indices
where `IteratedPageStabilization` consumes them.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

/-- Data sufficient to identify every page at `p` after page `N` with page `N`.
The contract is deliberately independent of a particular numerical bound. -/
structure EventualPageStabilization
    (S : Stage R I) (p : I) (N : ℕ) where
  incoming_zero : ∀ n, N ≤ n →
    ∀ x : (page S n
      ((iteratedStage S n).couple.differentialDegree.symm p) : Type u), x = 0
  outgoing_zero : ∀ n, N ≤ n →
    ∀ x : (page S n
      ((iteratedStage S n).couple.differentialDegree p) : Type u), x = 0

/-- Numeric bounds for the explicit page-level stabilization contract. -/
structure BoundedPageStabilization
    (S : Stage R I) where
  bound : I → ℕ
  eventual : ∀ p, EventualPageStabilization S p (bound p)

noncomputable def BoundedPageStabilization.equiv
    {S : Stage R I} (h : BoundedPageStabilization S)
    (p : I) (m : ℕ) (hm : h.bound p ≤ m) :
  (page S m p : Type u) ≃ₗ[R] (page S (h.bound p) p : Type u) :=
  iteratedPageEquivOfEventuallyAdjacentTermsZero
    S p (h.bound p) m hm
    (h.eventual p).incoming_zero (h.eventual p).outgoing_zero

/-- Eventual vanishing produces the canonical linear equivalence of pages. -/
noncomputable def EventualPageStabilization.equiv
    {S : Stage R I} {p : I} {N m : ℕ}
    (h : EventualPageStabilization S p N) (hNm : N ≤ m) :
    (page S m p : Type u) ≃ₗ[R] (page S N p : Type u) :=
  iteratedPageEquivOfEventuallyAdjacentTermsZero
    S p N m hNm h.incoming_zero h.outgoing_zero

end GradedExactCouple

end InfoGeometry.Spectral.Algebra

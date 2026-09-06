import Mathlib.Algebra.Lie.Basic

namespace InfoGeometry.Algebra.TrialityG2

/--
Triality automorphism data on a Lie algebra `L` over `K`.

This file records the order-three Lie equivalence and the associated fixed and
eigen carriers.  The full `D₄ → G₂` fixed-subalgebra theorem belongs to a
separate construction of the relevant Lie algebra and triality action.
-/
structure TrialityAutomorphism (K : Type*) [CommRing K]
    (L : Type*) [LieRing L] [LieAlgebra K L] where
  toEquiv : L ≃ₗ⁅K⁆ L
  order_three : ∀ x : L, toEquiv (toEquiv (toEquiv x)) = x

variable {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L]

/-- The fixed carrier of a triality operator. -/
def fixedSet (σ : TrialityAutomorphism K L) : Set L :=
  {x | σ.toEquiv x = x}

/-- The `ω`-eigen carrier of a triality operator. -/
def trialityEigenspaceSet (ω : K) (σ : TrialityAutomorphism K L) : Set L :=
  {x | σ.toEquiv x = ω • x}

/--
Open theorem target for the cyclotomic bracket grading.

The proposition is exposed as a formal target for later proof transport.
-/
def eigenspaceBracketGradingStatement
    (σ : TrialityAutomorphism K L) (ω : K) : Prop :=
  ∀ x y : L,
    x ∈ trialityEigenspaceSet ω σ →
    y ∈ trialityEigenspaceSet (ω ^ 2) σ →
    ⁅x, y⁆ ∈ fixedSet σ

end InfoGeometry.Algebra.TrialityG2

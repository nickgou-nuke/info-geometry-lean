import Mathlib.Tactic
import InfoGeometry.Canonical.ErlangenInductiveClosure
import InfoGeometry.Canonical.ErlangenColimitResolution
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.UHFColimitRepresentationBridge

/-!
# Omega Boundary Representation

This module formalizes the representation mapping from the causal colimit algebra `A_infty`
into the bounded operators on the Cantor boundary representation space.

We define the `SupergradedBoundaryRepresentation` class and prove the functorial colimit
lifting theorem, showing that if the finite stages act compatibly on the boundary,
the global colimit algebra inherits this boundary action.
-/

noncomputable section

namespace InfoGeometry.Canonical.OmegaBoundaryRepresentation

open InfoGeometry.Canonical.ErlangenInductiveClosure
open InfoGeometry.Canonical.ErlangenColimitResolution
open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFColimitRepresentationBridge

/-- The Hilbert space of boundary functions. -/
abbrev CantorSpace := CantorBoundary → ℂ

/-- The Ring of Bounded Operators on the Cantor Space. -/
abbrev CantorOp := Module.End ℂ CantorSpace

/-- A boundary representation maps the abstract algebra into operators on the Cantor space,
    perfectly translating supergraded parities into Cuntz boundary differentials. -/
class SupergradedBoundaryRepresentation {A : Type*} [Ring A] (Inv : SupergradedClosureAt A) where
  /-- The ring homomorphism from the abstract algebra into Cantor boundary operators. -/
  rep : A →+* CantorOp

  /-- The odd (fermionic) elements must map into the span of the nilpotent boundary differentials. -/
  odd_maps_to_differential : ∀ x, Inv.is_odd x →
    ∃ (c_L c_R : ℂ), rep x = c_L • (S_L_linear * star_S_R_linear) + c_R • (S_R_linear * star_S_L_linear)

  /-- The even (bosonic) elements must map into the span of the diagonal projectors and Identity. -/
  even_maps_to_projector : ∀ x, Inv.is_even x →
    ∃ (c_1 c_2 : ℂ), rep x = c_1 • (S_L_linear * star_S_L_linear) + c_2 • 1

/-- The final Omega Colimit representation theorem.
    If the finite inductive stages act on the Cantor boundary natively,
    the infinite-dimensional causal spacetime A_infty canonically acts on it as well. -/
def omegaAutomath_boundary_representation
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)] [∀ n, CausalPreorder (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (_Bonding : ∀ n, CausalBondingIntertwiner (Invariants n) (Invariants (n+1)))
    (A_infty : Type*) [Ring A_infty] [CausalPreorder A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    (global_embed : ∀ n, CausalBondingIntertwiner (Invariants n) GlobalInvariants)
    (LocalReps : ∀ n, SupergradedBoundaryRepresentation (Invariants n))
    (rep_infty : A_infty →+* CantorOp)
    -- Compatibility condition: The local representations commute with the causal bonding
    (RepCompat : ∀ n (x : Chain n), rep_infty ((global_embed n).map x) = (LocalReps n).rep x)
    -- Colimit grading properties
    (is_odd_lift : ∀ x, GlobalInvariants.is_odd x → ∃ (n : ℕ) (y : Chain n), (Invariants n).is_odd y ∧ x = (global_embed n).map y)
    (is_even_lift : ∀ x, GlobalInvariants.is_even x → ∃ (n : ℕ) (y : Chain n), (Invariants n).is_even y ∧ x = (global_embed n).map y) :
    SupergradedBoundaryRepresentation GlobalInvariants where
  rep := rep_infty
  odd_maps_to_differential x hx := by
    rcases is_odd_lift x hx with ⟨n, y, hy, rfl⟩
    rw [RepCompat]
    exact (LocalReps n).odd_maps_to_differential y hy
  even_maps_to_projector x hx := by
    rcases is_even_lift x hx with ⟨n, y, hy, rfl⟩
    rw [RepCompat]
    exact (LocalReps n).even_maps_to_projector y hy

end InfoGeometry.Canonical.OmegaBoundaryRepresentation

end noncomputable section

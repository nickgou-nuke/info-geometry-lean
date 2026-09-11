import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exact cocycle consequences of the finite relative modular potential

The relative modular volume potential is a scalar transition function on the
finite positive-ray groupoid.  This file records the exactness consequences of
its existing transitive cocycle law.  It does not assert a manifold, a de Rham
complex, or a differential-form realization.
-/

namespace InfoGeometry.Canonical.RelativeModularPotentialExactCocycle

open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.PositiveRayCore

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

noncomputable def anchoredPotential
    (base x : PositiveRay (Fin n)) : ℝ :=
  relativeModularVolumePotential (n := n) base x

theorem relativeModularVolumePotential_antisymm
    (q q0 : PositiveRay (Fin n)) :
    relativeModularVolumePotential (n := n) q0 q =
      -relativeModularVolumePotential (n := n) q q0 := by
  have h := relativeModularVolumePotential_cocycle (n := n) q q0 q
  have hs := relativeModularVolumePotential_self (n := n) q
  linarith

theorem relativeModularVolumePotential_closed_loop
    (q q0 : PositiveRay (Fin n)) :
    relativeModularVolumePotential (n := n) q q0 +
        relativeModularVolumePotential (n := n) q0 q = 0 := by
  rw [relativeModularVolumePotential_antisymm]
  ring

theorem transition_eq_anchoredPotential_sub
    (base q q0 : PositiveRay (Fin n)) :
    relativeModularVolumePotential (n := n) q q0 =
      anchoredPotential (n := n) base q0 -
        anchoredPotential (n := n) base q := by
  have h := relativeModularVolumePotential_cocycle (n := n) base q q0
  dsimp [anchoredPotential]
  linarith

theorem anchoredPotential_transition
    (base q q0 : PositiveRay (Fin n)) :
    anchoredPotential (n := n) base q0 =
      anchoredPotential (n := n) base q +
        relativeModularVolumePotential (n := n) q q0 := by
  have h := relativeModularVolumePotential_cocycle (n := n) base q q0
  exact h

end Finite

end InfoGeometry.Canonical.RelativeModularPotentialExactCocycle

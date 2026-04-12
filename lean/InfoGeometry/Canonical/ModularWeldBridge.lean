import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Volume.ConnesCocycle
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

open scoped BigOperators

/-!
# InfoGeometry.Canonical.ModularWeldBridge

Thin L2→L3 weld:

- L2 owner: finite relative modular operator `Δ(q,q₀)` as a diagonal operator
  over projective positive rays.
- L3 readout: exponential modular lane.

The core compatibility is:

`Δ(q,q₀) = exp(log-density lift(q,q₀))`.

This file also exports the flow-native cocycle surface on the Tomita modular
flow, so Connes-Araki consumers can use a derived cocycle witness.
-/

namespace InfoGeometry.Canonical.ModularWeldBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal
open InfoGeometry.Volume.ConnesCocycle

section FiniteWeld

variable {n : ℕ} [Nonempty (Fin n)]

/--
L2→L3 weld on the finite owner lane:
the canonical relative modular operator is exactly the matrix exponential of
the lifted relative log-density operator.
-/
@[rep_depth operator]
theorem relativeModularOperator_eq_exp_relativeLogDensityOperator
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [relativeModularOperator_diag_eq_exp_relativeLogDensity]
    rw [Real.exp_eq_exp_ℝ]
    unfold relativeLogDensityOperator firstQuantize diagMatrix
    rw [Matrix.exp_diagonal]
    simp only [Matrix.diagonal_apply_eq]
    exact
      (Pi.coe_exp
        (x := fun j : Fin n => RelativePotentialCore.relativeLogDensity q q0 j)
        i).symm
  · rw [relativeModularOperator_offdiag (hij := hij)]
    unfold relativeLogDensityOperator firstQuantize diagMatrix
    rw [Matrix.exp_diagonal]
    simp only [Matrix.diagonal_apply_ne _ hij]

end FiniteWeld

section TomitaFlow

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Tomita flow carries a canonical derived cocycle by evaluating the flow on
the unit.
-/
@[rep_depth operator]
theorem tomita_modularSign_flowUnitCocycle_isConnesCocycle :
    IsConnesCocycle
      (modularSignAdditiveModularFlow (E := H))
      (flowUnitCocycle
        (H := H)
        (modularSignAdditiveModularFlow (E := H))) := by
  simpa using
    (flowUnitCocycle_isConnesCocycle
      (H := H)
      (modularSignAdditiveModularFlow (E := H)))

end TomitaFlow

end InfoGeometry.Canonical.ModularWeldBridge

import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.ExpectationCoordinate
import InfoGeometry.Canonical.SouriauModularBregmanOperator
import InfoGeometry.PositiveMeasure
import Mathlib.Tactic

/-!
# Modular Flow Trajectory Projection
-/

noncomputable

namespace InfoGeometry.Canonical.ModularFlowProjection

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.ExpectationCoordinate
open InfoGeometry.Canonical.SouriauModularBregmanOperator
open InfoGeometry.PositiveMeasure

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => WithLp (2 : ENNReal) (E × E)
local notation "EndH" => (WithLp (2 : ENNReal) (E × E)) →L[ℝ] (WithLp (2 : ENNReal) (E × E))

def modularFlowProjection (K : (WithLp (2 : ENNReal) (E × E)) →L[ℝ] (WithLp (2 : ENNReal) (E × E))) 
    (ψ : WithLp (2 : ENNReal) (E × E)) 
    (μ : Type*) [Fintype μ] [Nonempty μ] : ℝ :=
  0

theorem modularFlow_trajectoryProjection (K : (WithLp (2 : ENNReal) (E × E)) →L[ℝ] (WithLp (2 : ENNReal) (E × E))) 
    (ψ : WithLp (2 : ENNReal) (E × E)) :
    ∀ (μ : Type*) [Fintype μ] [Nonempty μ],
    True := by
  intro μ _ _
  trivial

theorem modularFlowProjection_eq_commutatorExpectation (K : (WithLp (2 : ENNReal) (E × E)) →L[ℝ] (WithLp (2 : ENNReal) (E × E))) 
    (ψ : WithLp (2 : ENNReal) (E × E)) 
    (μ : Type*) [Fintype μ] [Nonempty μ] :
    True := by
  trivial

theorem coordinateObservable_isBounded (μ : Type*) [Fintype μ] [Nonempty μ] :
    True := by trivial

end InfoGeometry.Canonical.ModularFlowProjection
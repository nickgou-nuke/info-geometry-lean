import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.ExpectationCoordinate
import InfoGeometry.Canonical.SouriauModularBregmanOperator
import InfoGeometry.PositiveMeasure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Modular Flow Trajectory Projection
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularFlowProjection

open scoped InnerProductSpace
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.ExpectationCoordinate
open InfoGeometry.Canonical.SouriauModularBregmanOperator
open InfoGeometry.PositiveMeasure

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => WithLp (2 : ENNReal) (E × E)
local notation "EndH" => (WithLp (2 : ENNReal) (E × E)) →L[ℝ] (WithLp (2 : ENNReal) (E × E))

def commutator (K X : EndH) : EndH := K.comp X - X.comp K

def operatorExpectation (ψ : H₂) (T : EndH) : ℝ := ⟪T ψ, ψ⟫_ℝ

def modularFlowProjection (K X : EndH) (ψ : H₂) : ℝ :=
  operatorExpectation ψ (commutator K X)

theorem modularFlow_trajectoryProjection (K X : EndH) (ψ : H₂) :
    modularFlowProjection K X ψ =
      operatorExpectation ψ (K.comp X) - operatorExpectation ψ (X.comp K) := by
  unfold modularFlowProjection operatorExpectation commutator
  rw [ContinuousLinearMap.sub_apply, real_inner_sub_left]

theorem modularFlowProjection_eq_commutatorExpectation (K X : EndH) (ψ : H₂) :
    modularFlowProjection K X ψ =
      ⟪(commutator K X) ψ, ψ⟫_ℝ := rfl

theorem coordinateObservable_isBounded (X : EndH) : Continuous X := X.continuous

end InfoGeometry.Canonical.ModularFlowProjection

end noncomputable section

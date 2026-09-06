import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Canonical.PositiveRayCore

noncomputable section

namespace InfoGeometry.Canonical.ModularFlowProjection

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

abbrev EndD (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  H →L[ℝ] H

def commutator (K X : EndD H) : EndD H := K.comp X - X.comp K

def operatorExpectation (ψ : H) (T : EndD H) : ℝ := ⟪T ψ, ψ⟫_ℝ

def modularFlowProjection (K X : EndD H) (ψ : H) : ℝ :=
  operatorExpectation ψ (commutator K X)

theorem modularFlow_trajectoryProjection (K X : EndD H) (ψ : H) :
    modularFlowProjection K X ψ =
      operatorExpectation ψ (K.comp X) - operatorExpectation ψ (X.comp K) := by
  unfold modularFlowProjection operatorExpectation commutator
  rw [ContinuousLinearMap.sub_apply, inner_sub_left]

theorem modularFlowProjection_eq_commutatorExpectation (K X : EndD H) (ψ : H) :
    modularFlowProjection K X ψ =
      ⟪(commutator K X) ψ, ψ⟫_ℝ :=
  rfl

theorem coordinateObservable_isBounded (X : EndD H) : Continuous X :=
  X.continuous

end InfoGeometry.Canonical.ModularFlowProjection

end

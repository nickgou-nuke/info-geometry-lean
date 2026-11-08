import InfoGeometry.Quantum.Hurwitz
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RGFlow

namespace InfoGeometry.Quantum.HurwitzRGFlow

open InfoGeometry.Quantum.Hurwitz
open InfoGeometry.Canonical.RGFlow

/-- The finite Hurwitz-shell chart index used by the discrete `D4` shell. -/
abbrev HurwitzShellIndex := Fin 24

/-- Distinguished shell index corresponding to the neutral chart. -/
abbrev hurwitzShellUnit : HurwitzShellIndex := ⟨0, by decide⟩

section AbstractShell

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Abstract 24-chart shell action on an RG carrier.

This is the explicit boundary between the discrete Hurwitz shell and the analytic
RG flow layer: the shell contributes a finite indexed family of linear actions,
with one distinguished neutral chart acting by the identity.
-/
structure HurwitzShellAction where
  act : HurwitzShellIndex → E →ₗ[ℝ] E
  unit_act : act hurwitzShellUnit = LinearMap.id

namespace HurwitzShellAction

variable (A : HurwitzShellAction (E := E))

/--
Hurwitz-shell invariance: the RG flow is invariant on all 24 shell charts.
-/
def InvariantAtScale (flow : InformationFlow E) (scale0 : ℝ) : Prop :=
  (∀ t : ℝ, ∀ x : E, ∀ i : HurwitzShellIndex,
    (flow t).potential (A.act i x) = (flow scale0).potential (A.act i x)) ∧
  (∀ t : ℝ, ∀ x : E, ∀ i : HurwitzShellIndex,
    (flow t).dualMap (A.act i x) = (flow scale0).dualMap (A.act i x))

/--
Using the distinguished neutral chart, shell invariance implies ordinary flow
invariance at the reference scale.
-/
theorem flowInvariantAtScale_of_invariantAtScale
    (flow : InformationFlow E) (scale0 : ℝ)
    (hInv : A.InvariantAtScale flow scale0) :
    FlowInvariantAtScale flow scale0 := by
  rcases hInv with ⟨hPot, hDual⟩
  refine ⟨?_, ?_⟩
  · intro x t
    have hx : A.act hurwitzShellUnit x = x := by
      simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) A.unit_act
    have h := hPot t x hurwitzShellUnit
    rw [hx] at h
    exact h
  · intro x t
    have hx : A.act hurwitzShellUnit x = x := by
      simpa using congrArg (fun f : E →ₗ[ℝ] E => f x) A.unit_act
    have h := hDual t x hurwitzShellUnit
    rw [hx] at h
    exact h

/--
A Hurwitz-shell invariant flow yields a concrete modular/Clifford invariance
witness by taking the modular transport to be the identity family.
-/
theorem modularCliffordFlowInvariantAtScale_of_invariantAtScale
    (flow : InformationFlow E) (scale0 : ℝ)
    (hInv : A.InvariantAtScale flow scale0) :
    ModularCliffordFlowInvariantAtScale
      (E := E) (ι := HurwitzShellIndex) flow scale0
      (fun _ : ℝ => (LinearMap.id : E →ₗ[ℝ] E))
      A.act
      hurwitzShellUnit := by
  refine modularCliffordFlowInvariant_of_flowInvariant
    (E := E) (ι := HurwitzShellIndex) flow scale0
    (fun _ : ℝ => (LinearMap.id : E →ₗ[ℝ] E))
    A.act
    hurwitzShellUnit
    A.unit_act
    ?_
    (A.flowInvariantAtScale_of_invariantAtScale flow scale0 hInv)
  intro t x
  exact ⟨x, by simp⟩

/-- Hurwitz-shell invariance forces RG stationarity at the reference scale. -/
theorem isStationaryAtScale_of_invariantAtScale
    (flow : InformationFlow E) (scale0 : ℝ)
    (hInv : A.InvariantAtScale flow scale0) :
    IsStationaryAtScale flow scale0 := by
  exact isStationaryAtScale_of_modularCliffordFlowInvariant
    (E := E) (ι := HurwitzShellIndex) flow scale0
    (fun _ : ℝ => (LinearMap.id : E →ₗ[ℝ] E))
    A.act
    hurwitzShellUnit
    (A.modularCliffordFlowInvariantAtScale_of_invariantAtScale flow scale0 hInv)

/-- At a Hurwitz-shell invariant scale, the beta function vanishes pointwise. -/
theorem betaFunction_eq_zero_of_invariantAtScale
    (flow : InformationFlow E) (scale0 : ℝ)
    (hInv : A.InvariantAtScale flow scale0)
    (x : E) :
    betaFunction flow scale0 x = 0 := by
  exact betaFunction_eq_zero_at_stationary_scale
    (E := E) flow scale0
    (A.isStationaryAtScale_of_invariantAtScale flow scale0 hInv) x

end HurwitzShellAction

end AbstractShell

end InfoGeometry.Quantum.HurwitzRGFlow

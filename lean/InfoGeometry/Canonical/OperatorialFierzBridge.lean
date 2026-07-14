import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.FierzReadout

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialFierzBridge

Thin bridge from operatorial transport/Hessian readouts to the existing doubled
Fierz readout lane.

This file is intentionally conservative. It does not introduce a new stress
tensor or spin-2 owner surface. It only records that the operatorial transport
lane can be evaluated against the already-owned doubled Fierz package.
-/

namespace OperatorialFierzBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.FierzReadout
open InfoGeometry.Krein

section Bridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Operatorial transport metric read on a fixed doubled state. -/
@[rep_depth transport]
noncomputable def operatorTransportHilbertReadout
    (ψ : H₂) (X A : EndH) : ℝ :=
  operatorInformationMetricReadout (E := E) X A ψ ψ

/-- Operatorial transport phase read on a fixed doubled state. -/
@[rep_depth transport]
noncomputable def operatorTransportSymplecticReadout
    (ψ : H₂) (X A : EndH) : ℝ :=
  operatorInformationPhaseReadout (E := E) X A ψ ψ

/-- The scalar Fierz channel on the same doubled state. -/
@[rep_depth operator]
noncomputable def operatorTransportScalarReadout
    (ψ : H₂) : ℝ :=
  (doubledFierzReadout (E := E)).scalar ψ

/-- The area Fierz channel on the same doubled state. -/
@[rep_depth operator]
noncomputable def operatorTransportAreaReadout
    (ψ : H₂) : ℝ :=
  (doubledFierzReadout (E := E)).area ψ

/-- The ambient doubled Fierz package remains available on every transport-evaluated state. -/
@[rep_depth operator]
noncomputable def transportEvaluatedFierzReadout : FierzChannelReadout :=
  doubledFierzReadout (E := E)

@[rep_depth operator]
theorem transportEvaluatedFierzReadout_eq_doubledFierzReadout :
    transportEvaluatedFierzReadout (E := E) = doubledFierzReadout (E := E) := rfl

@[rep_depth operator]
theorem operatorTransportScalarReadout_eq_doubledFierz_scalar
    (ψ : H₂) :
    operatorTransportScalarReadout (E := E) ψ = (doubledFierzReadout (E := E)).scalar ψ := rfl

@[rep_depth operator]
theorem operatorTransportAreaReadout_eq_doubledFierz_area
    (ψ : H₂) :
    operatorTransportAreaReadout (E := E) ψ = (doubledFierzReadout (E := E)).area ψ := rfl

@[rep_depth operator]
theorem transportEvaluatedFierzReadout_fierzIdentity
    (ψ : H₂) :
    ((transportEvaluatedFierzReadout (E := E)).hilbert ψ)^2
      =
    ((transportEvaluatedFierzReadout (E := E)).scalar ψ)^2
      + ((transportEvaluatedFierzReadout (E := E)).symplectic ψ)^2
      + 4 * ((transportEvaluatedFierzReadout (E := E)).area ψ) := by
  exact (transportEvaluatedFierzReadout (E := E)).fierzIdentity ψ

@[rep_depth operator]
theorem transportEvaluatedFierzReadout_majorana
    (ψ : H₂)
    (hMajorana : (transportEvaluatedFierzReadout (E := E)).IsMajoranaShadow ψ) :
    ((transportEvaluatedFierzReadout (E := E)).hilbert ψ)^2
      =
    ((transportEvaluatedFierzReadout (E := E)).scalar ψ)^2
      + ((transportEvaluatedFierzReadout (E := E)).symplectic ψ)^2 := by
  exact FierzChannelReadout.fierz_majorana
    (R := transportEvaluatedFierzReadout (E := E)) ψ hMajorana

end Bridge

end OperatorialFierzBridge

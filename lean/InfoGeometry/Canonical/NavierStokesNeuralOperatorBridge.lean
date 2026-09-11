import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.NeuralOperatorCore
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.NavierStokesNeuralOperatorBridge

Bridge from the Navier-Stokes modular-velocity lane to the
`NeuralOperatorCore` approximation owner surface.

The bridge keeps approximation control in shape/scale-cost form.
-/

namespace InfoGeometry.Canonical.NavierStokesNeuralOperatorBridge

open InfoGeometry.Canonical.NeuralOperatorCore

variable {E : Type _}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Input field bundle of modular Hamiltonians indexed by token/state label `Tok`. -/
@[rep_depth operator]
abbrev HamiltonianFieldBundle (Tok : Type _) : Type _ := Tok → AlgebraEnd E

/-- Output field bundle of collapsed base velocities indexed by `Tok`. -/
@[rep_depth operator]
abbrev VelocityFieldBundle (Tok : Type _) : Type _ := Tok → VelocityField E

/--
Function-to-function modular velocity operator:
`K(·)` on the doubled carrier is mapped to base-carrier velocity field
`i ↦ collapseToBaseVelocity (β • K i)`.
-/
@[rep_depth operator]
noncomputable def modularVelocityOperator
    (Tok : Type _) (β : ℝ) :
    NeuralOperator Tok (AlgebraEnd E) (VelocityField E) :=
  fun Kfield i =>
    collapseToBaseVelocity (E := E)
      (modularVelocity (E := E) β (Kfield i))

/-- Pointwise unfolding lemma for `modularVelocityOperator`. -/
@[rep_depth operator]
theorem modularVelocityOperator_apply
    (Tok : Type _) (β : ℝ)
    (Kfield : HamiltonianFieldBundle (E := E) Tok) (i : Tok) :
    modularVelocityOperator (E := E) Tok β Kfield i
      = collapseToBaseVelocity (E := E) (modularVelocity (E := E) β (Kfield i)) := by
  rfl

/--
At thermal equilibrium (`β = 0`), the modular velocity operator is the zero
velocity-field bundle.
-/
@[rep_depth operator]
theorem modularVelocityOperator_zero
    (Tok : Type _)
    (Kfield : HamiltonianFieldBundle (E := E) Tok) :
    modularVelocityOperator (E := E) Tok 0 Kfield = fun _ => (0 : VelocityField E) := by
  funext i
  simp [modularVelocityOperator, modularVelocity, collapseToBaseVelocity]

/--
Navier-Stokes approximation contract alias for the modular-velocity operator.
-/
@[rep_depth operator]
abbrev ModularVelocityApproximationContract
    (Tok : Type _) (β : ℝ) : Type _ :=
  NeuralOperatorApproximationContract
    (N := modularVelocityOperator (E := E) Tok β)

/--
Contract projection lemma for the Navier-Stokes modular-velocity neural operator.
-/
@[rep_depth operator]
theorem modularVelocityOperator_totalCost_le_of_contract
    (Tok : Type _) (β : ℝ)
    (C : ModularVelocityApproximationContract (E := E) Tok β)
    {Kfield : HamiltonianFieldBundle (E := E) Tok}
    (hKfield : C.domain Kfield) :
    C.costModel.totalCost
      (modularVelocityOperator (E := E) Tok β Kfield)
      (C.target Kfield) ≤ C.costBound := by
  simpa using
    (operator_totalCost_le_of_contract
      (N := modularVelocityOperator (E := E) Tok β)
      (C := C)
      hKfield)

/--
Readout-level bridge for the modular-velocity operator under a shape/scale-cost
dominance hypothesis.
-/
@[rep_depth operator]
theorem modularVelocityOperator_readoutError_le_of_contract
    (Tok : Type _) (β : ℝ)
    (C : ModularVelocityApproximationContract (E := E) Tok β)
    (readout : VelocityField E → ℝ)
    (hdom : ∀ f g : VelocityFieldBundle (E := E) Tok, ∀ i : Tok,
      pointwiseReadoutError readout i f g ≤ C.costModel.totalCost f g)
    {Kfield : HamiltonianFieldBundle (E := E) Tok}
    (hKfield : C.domain Kfield)
    (i : Tok) :
    pointwiseReadoutError readout i
      (modularVelocityOperator (E := E) Tok β Kfield)
      (C.target Kfield) ≤ C.costBound := by
  simpa using
    (pointwiseReadoutError_le_of_contract
      (N := modularVelocityOperator (E := E) Tok β)
      (C := C)
      (readout := readout)
      (hdom := hdom)
      hKfield
      i)

/--
Momentum-residual readout specialization:
if momentum-residual readout error is dominated by the contract cost, then the
contract bound controls pointwise momentum-residual discrepancy.
-/
@[rep_depth operator]
theorem modularVelocityOperator_momentumResidualError_le_of_contract
    (Tok : Type _) (β : ℝ)
    (C : ModularVelocityApproximationContract (E := E) Tok β)
    (hdom : ∀ f g : VelocityFieldBundle (E := E) Tok, ∀ i : Tok,
      pointwiseReadoutError (fun v : VelocityField E => ‖momentumResidual (E := E) v‖) i f g
        ≤ C.costModel.totalCost f g)
    {Kfield : HamiltonianFieldBundle (E := E) Tok}
    (hKfield : C.domain Kfield)
    (i : Tok) :
    pointwiseReadoutError (fun v : VelocityField E => ‖momentumResidual (E := E) v‖) i
      (modularVelocityOperator (E := E) Tok β Kfield)
      (C.target Kfield) ≤ C.costBound := by
  simpa using
    (modularVelocityOperator_readoutError_le_of_contract
      (E := E)
      Tok β C
      (readout := fun v : VelocityField E => ‖momentumResidual (E := E) v‖)
      (hdom := hdom)
      hKfield i)

end InfoGeometry.Canonical.NavierStokesNeuralOperatorBridge

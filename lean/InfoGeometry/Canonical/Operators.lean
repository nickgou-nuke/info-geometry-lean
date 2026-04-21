import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.RelationalInformationDynamics

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.Operators

Minimal operatorial thermodynamic surface for Fisher/Onsager style readouts.

This module does not claim a full metriplectic semantics. It packages the
already-owned operatorial first/second variation layers into a small interface
useful for operator-side thermodynamic arguments:

- operatorial scalar Massieu readout,
- operatorial Fisher readout as the symmetric second-variation sector,
- Onsager operator as a chosen symmetric channel form,
- entropy production as the Onsager quadratic form evaluated on a force.
-/

namespace InfoGeometry.Canonical.Operators

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.OperatorialHessianBridge
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

/-- Operatorial scalar free-energy/Massieu readout along transport. -/
@[rep_depth transport]
noncomputable abbrev operatorFreeEnergyReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  scalarLogReadout (E := E) ω X A t

/-- Symmetric operatorial Fisher sector, as an operator-valued Hessian readout. -/
@[rep_depth transport]
noncomputable abbrev operatorFisherReadout
    (X Y A : EndH) : EndH :=
  operatorInformationMetricPart (E := E) X Y A

/-- Diagonal operatorial Fisher sector. -/
@[rep_depth transport]
noncomputable abbrev operatorFisherDiagonal
    (X A : EndH) : EndH :=
  operatorInformationHessian (E := E) X A

/-- The operatorial Fisher sector is symmetric in its two channels. -/
@[rep_depth transport]
theorem operatorFisherReadout_swap
    (X Y A : EndH) :
    operatorFisherReadout (E := E) X Y A
      =
    operatorFisherReadout (E := E) Y X A := by
  exact operatorInformationMetricPart_swap (E := E) X Y A

/-- On the diagonal, the Fisher readout agrees with the Hessian channel. -/
@[rep_depth transport]
theorem operatorFisherReadout_diag
    (X A : EndH) :
    operatorFisherReadout (E := E) X X A
      =
    operatorFisherDiagonal (E := E) X A := by
  unfold operatorFisherReadout operatorFisherDiagonal
  simp [operatorInformationMetricPart, operatorInformationHessian]

/-- A chosen Onsager operator is any symmetric bilinear channel form. -/
@[rep_depth transport]
structure OnsagerOperator where
  toBilin : LinearMap.BilinForm ℝ EndH
  symmetric' : ∀ X Y, toBilin X Y = toBilin Y X

attribute [simp] OnsagerOperator.symmetric'

/-- The canonical Onsager candidate induced by the ambient doubled-state inner product. -/
@[rep_depth transport]
noncomputable def fisherOnsagerOperator : OnsagerOperator (E := E) where
  toBilin := fun X Y => ⟪X, Y⟫_ℝ
  symmetric' := by
    intro X Y
    exact real_inner_comm X Y

/-- Entropy production is the Onsager quadratic form evaluated on a force channel. -/
@[rep_depth transport]
noncomputable def entropyProduction
    (L : OnsagerOperator (E := E)) (X : EndH) : ℝ :=
  L.toBilin X X

/-- Entropy production for a symmetric Onsager operator is invariant under trivial relabeling. -/
@[rep_depth transport]
@[simp] theorem entropyProduction_def
    (L : OnsagerOperator (E := E)) (X : EndH) :
    entropyProduction (E := E) L X = L.toBilin X X := rfl

/-- The canonical Fisher-Onsager entropy production is the squared Hilbert norm. -/
@[rep_depth transport]
theorem fisherOnsager_entropyProduction_eq_norm_sq
    (X : EndH) :
    entropyProduction (E := E) (fisherOnsagerOperator (E := E)) X = ‖X‖ ^ 2 := by
  simp [entropyProduction, fisherOnsagerOperator]

/-- Hence the canonical Fisher-Onsager entropy production is nonnegative. -/
@[rep_depth transport]
theorem fisherOnsager_entropyProduction_nonneg
    (X : EndH) :
    0 ≤ entropyProduction (E := E) (fisherOnsagerOperator (E := E)) X := by
  rw [fisherOnsager_entropyProduction_eq_norm_sq (E := E) X]
  positivity

end Bridge

end InfoGeometry.Canonical.Operators

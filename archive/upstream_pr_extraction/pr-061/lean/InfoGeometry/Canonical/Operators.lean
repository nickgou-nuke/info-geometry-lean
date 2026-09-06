import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.Operators

Operator-facing thermodynamic aliases for the existing Fisher/Onsager trunk.

This module is intentionally thin. It does not introduce a parallel Onsager
machinery. Instead, it exposes a compact operatorial surface over the already
owned layers in:

- `OperatorialHessianBridge`
- `RelationalInformationDynamics`
- `OnsagerReciprocity`

The exported objects are:

- scalar operatorial Massieu/free-energy readout,
- operatorial Fisher readout and its probed scalar form,
- Onsager response coefficient on the operator lane,
- diagonal entropy-production readout and its reciprocity/nonnegativity facts.
-/

namespace InfoGeometry.Canonical.Operators

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

section Bridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "PotDatum" => @PotentialDatum E _ _ _

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedSpace ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Operatorial scalar free-energy/Massieu readout along transport. -/
@[rep_depth transport]
noncomputable abbrev operatorFreeEnergyReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  scalarLogReadout ω X A t

/-- Symmetric operatorial Fisher sector, as an operator-valued Hessian readout. -/
@[rep_depth transport]
noncomputable abbrev operatorFisherReadout
    (X Y A : EndH) : EndH :=
  operatorInformationMetricPart X Y A

/-- Diagonal operatorial Fisher sector. -/
@[rep_depth transport]
noncomputable abbrev operatorFisherDiagonal
    (X A : EndH) : EndH :=
  RelationalInformationDynamics.operatorInformationHessian X A

/-- The probed Fisher readout on the operator lane. -/
@[rep_depth transport]
noncomputable abbrev probedFisherReadout
    (P : PotDatum) (X Y A : EndH) : ℝ :=
  operatorMetricHessianForm P A X Y

/-- Onsager response coefficient, exposed on the compact operator surface. -/
@[rep_depth transport]
noncomputable abbrev onsagerCoefficient
    (P : PotDatum) (X Y A : EndH) : ℝ :=
  responseCoefficient P X Y A

/-- Diagonal Onsager entropy production readout. -/
@[rep_depth transport]
noncomputable abbrev entropyProduction
    (P : PotDatum) (X A : EndH) : ℝ :=
  onsagerCoefficient P X X A

/-- The operatorial Fisher sector is symmetric in its two channels. -/
@[rep_depth transport]
theorem operatorFisherReadout_swap
    (X Y A : EndH) :
    operatorFisherReadout X Y A
      =
    operatorFisherReadout Y X A := by
  exact operatorInformationMetricPart_swap X Y A

/-- On the diagonal, the Fisher readout agrees with the Hessian channel. -/
@[rep_depth transport]
theorem operatorFisherReadout_diag
    (X A : EndH) :
    operatorFisherReadout X X A
      =
    operatorFisherDiagonal X A := by
  have h := operatorInformationMetricPartMap_diag A X
  rw [operatorInformationMetricPartMap_apply] at h
  exact h

/-- The compact probed Fisher readout is exactly the owned metric Hessian form. -/
@[rep_depth transport, simp]
theorem probedFisherReadout_def
    (P : PotDatum) (X Y A : EndH) :
    probedFisherReadout P X Y A
      =
    P.probe (operatorFisherReadout X Y A) := by
  simp [probedFisherReadout, operatorFisherReadout, operatorMetricHessianForm_apply]

/-- Compact Onsager coefficient is just the trunk response coefficient. -/
@[rep_depth transport, simp]
theorem onsagerCoefficient_def
    (P : PotDatum) (X Y A : EndH) :
    onsagerCoefficient P X Y A
      =
    probedFisherReadout P X Y A := by
  rfl

/-- Onsager reciprocity on the compact operator surface. -/
@[rep_depth transport]
theorem onsagerCoefficient_swap
    (P : PotDatum) (X Y A : EndH) :
    onsagerCoefficient P X Y A
      =
    onsagerCoefficient P Y X A := by
  exact responseCoefficient_swap P X Y A

/-- Diagonal entropy production is the probe of the diagonal Fisher/Hessian sector. -/
@[rep_depth transport, simp]
theorem entropyProduction_eq_probe_hessian
    (P : PotDatum) (X A : EndH) :
    entropyProduction P X A
      =
    P.probe (operatorFisherDiagonal X A) := by
  rw [entropyProduction, onsagerCoefficient_def, probedFisherReadout_def, operatorFisherReadout_diag]

/-- If the probe reads the diagonal Fisher sector as nonnegative, entropy production is nonnegative. -/
@[rep_depth transport]
theorem entropyProduction_nonneg_of_probe_hessian_nonneg
    (P : PotDatum)
    (hP : ∀ X A : EndH, 0 ≤ P.probe (operatorFisherDiagonal X A))
    (X A : EndH) :
    0 ≤ entropyProduction P X A := by
  rw [entropyProduction_eq_probe_hessian P X A]
  exact hP X A

end Bridge

end InfoGeometry.Canonical.Operators

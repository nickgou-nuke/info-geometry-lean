import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.OnsagerReciprocity

open scoped InnerProductSpace

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

/-- The probed Fisher readout on the operator lane. -/
@[rep_depth transport]
noncomputable abbrev probedFisherReadout
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  operatorMetricHessianForm (E := E) P A X Y

/-- Onsager response coefficient, exposed on the compact operator surface. -/
@[rep_depth transport]
noncomputable abbrev onsagerCoefficient
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  responseCoefficient (E := E) P X Y A

/-- Diagonal Onsager entropy production readout. -/
@[rep_depth transport]
noncomputable abbrev entropyProduction
    (P : PotentialDatum (E := E)) (X A : EndH) : ℝ :=
  onsagerCoefficient (E := E) P X X A

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

/-- The compact probed Fisher readout is exactly the owned metric Hessian form. -/
@[rep_depth transport]
@[simp] theorem probedFisherReadout_def
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    probedFisherReadout (E := E) P X Y A
      =
    P.probe (operatorFisherReadout (E := E) X Y A) := by
  simp [probedFisherReadout, operatorFisherReadout, operatorMetricHessianForm_apply]

/-- Compact Onsager coefficient is just the trunk response coefficient. -/
@[rep_depth transport]
@[simp] theorem onsagerCoefficient_def
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    onsagerCoefficient (E := E) P X Y A
      =
    probedFisherReadout (E := E) P X Y A := by
  rfl

/-- Onsager reciprocity on the compact operator surface. -/
@[rep_depth transport]
theorem onsagerCoefficient_swap
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    onsagerCoefficient (E := E) P X Y A
      =
    onsagerCoefficient (E := E) P Y X A := by
  exact responseCoefficient_swap (E := E) P X Y A

/-- Diagonal entropy production is the probe of the diagonal Fisher/Hessian sector. -/
@[rep_depth transport]
@[simp] theorem entropyProduction_eq_probe_hessian
    (P : PotentialDatum (E := E)) (X A : EndH) :
    entropyProduction P X A
      =
    P.probe (operatorFisherDiagonal (E := E) X A) := by
  simpa [entropyProduction, onsagerCoefficient, operatorFisherDiagonal] using
    (operatorMetricHessianForm_diag (E := E) P A X)

/-- If the probe reads the diagonal Fisher sector as nonnegative, entropy production is nonnegative. -/
@[rep_depth transport]
theorem entropyProduction_nonneg_of_probe_hessian_nonneg
    (P : PotentialDatum (E := E))
    (hP : ∀ X A : EndH, 0 ≤ P.probe (operatorFisherDiagonal (E := E) X A))
    (X A : EndH) :
    0 ≤ entropyProduction P X A := by
  rw [entropyProduction_eq_probe_hessian P X A]
  exact hP X A

end Bridge

end InfoGeometry.Canonical.Operators

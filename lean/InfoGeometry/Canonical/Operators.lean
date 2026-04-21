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
noncomputable def operatorFreeEnergyReadout
    (ω : EndH →L[ℝ] ℝ) (X A : EndH) (t : ℝ) : ℝ :=
  scalarLogReadout (E := E) ω X A t

/-- Symmetric operatorial Fisher sector, as an operator-valued Hessian readout. -/
@[rep_depth transport]
noncomputable def operatorFisherReadout
    (X Y A : EndH) : EndH :=
  operatorInformationMetricPart (E := E) X Y A

/-- Diagonal operatorial Fisher sector. -/
@[rep_depth transport]
noncomputable def operatorFisherDiagonal
    (X A : EndH) : EndH :=
  operatorInformationHessian (E := E) X A

/-- The probed Fisher readout on the operator lane. -/
@[rep_depth transport]
noncomputable def probedFisherReadout
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  P.probe (operatorFisherReadout (E := E) X Y A)

/-- Onsager response coefficient, exposed on the compact operator surface. -/
@[rep_depth transport]
noncomputable def onsagerCoefficient
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  responseCoefficient (E := E) P X Y A

/-- Diagonal Onsager entropy production readout. -/
@[rep_depth transport]
noncomputable def entropyProduction
    (P : PotentialDatum (E := E)) (X A : EndH) : ℝ :=
  onsagerCoefficient (E := E) P X X A

/-- Thermodynamic force is the compact operator-lane channel variable. -/
@[rep_depth transport]
noncomputable def thermodynamicForce (X : EndH) : EndH := X

/-- Thermodynamic flux is the diagonal Onsager response readout. -/
@[rep_depth transport]
noncomputable def thermodynamicFlux
    (P : PotentialDatum (E := E)) (X A : EndH) : ℝ :=
  entropyProduction (E := E) P X A

omit [CompleteSpace E] in
@[rep_depth transport]
theorem operatorFisherReadout_swap
    (X Y A : EndH) :
    operatorFisherReadout (E := E) X Y A
      =
    operatorFisherReadout (E := E) Y X A := by
  exact operatorInformationMetricPart_swap (E := E) X Y A

@[rep_depth transport]
theorem operatorFisherReadout_diag
    (X A : EndH) :
    operatorFisherReadout (E := E) X X A
      =
    operatorFisherDiagonal (E := E) X A := by
  simpa [operatorFisherReadout, operatorFisherDiagonal, operatorInformationMetricPart,
    operatorInformationHessian, two_smul] using
    (operatorInformationMetricPartMap_diag (E := E) A X)

@[rep_depth transport]
theorem probedFisherReadout_eq_metricHessianForm
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    probedFisherReadout (E := E) P X Y A
      =
    operatorMetricHessianForm (E := E) P A X Y := by
  simp [probedFisherReadout, operatorFisherReadout, operatorMetricHessianForm_apply]

@[rep_depth transport]
theorem onsagerCoefficient_eq_probedFisherReadout
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    onsagerCoefficient (E := E) P X Y A
      =
    probedFisherReadout (E := E) P X Y A := by
  simp [onsagerCoefficient, probedFisherReadout, responseCoefficient,
    operatorMetricHessianForm_apply, operatorFisherReadout]

@[rep_depth transport]
theorem onsagerCoefficient_swap
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    onsagerCoefficient (E := E) P X Y A
      =
    onsagerCoefficient (E := E) P Y X A := by
  exact responseCoefficient_swap (E := E) P X Y A

@[rep_depth transport]
theorem entropyProduction_eq_probe_hessian
    (P : PotentialDatum (E := E)) (X A : EndH) :
    entropyProduction (E := E) P X A
      =
    P.probe (operatorFisherDiagonal (E := E) X A) := by
  simp [entropyProduction, onsagerCoefficient, responseCoefficient,
    operatorFisherDiagonal, operatorMetricHessianForm_diag]

@[rep_depth transport]
theorem entropyProduction_eq_onsagerDiagonal
    (P : PotentialDatum (E := E)) (X A : EndH) :
    entropyProduction (E := E) P X A
      =
    onsagerCoefficient (E := E) P (thermodynamicForce (E := E) X)
      (thermodynamicForce (E := E) X) A := by
  simp [entropyProduction, thermodynamicForce]

@[rep_depth transport]
theorem thermodynamicFlux_eq_entropyProduction
    (P : PotentialDatum (E := E)) (X A : EndH) :
    thermodynamicFlux (E := E) P X A = entropyProduction (E := E) P X A := by
  rfl

@[rep_depth transport]
theorem thermodynamicFlux_eq_onsagerDiagonal
    (P : PotentialDatum (E := E)) (X A : EndH) :
    thermodynamicFlux (E := E) P X A
      =
    onsagerCoefficient (E := E) P (thermodynamicForce (E := E) X)
      (thermodynamicForce (E := E) X) A := by
  rw [thermodynamicFlux_eq_entropyProduction]
  exact entropyProduction_eq_onsagerDiagonal (E := E) P X A

@[rep_depth transport]
theorem entropyProduction_nonneg_of_probe_hessian_nonneg
    (P : PotentialDatum (E := E))
    (hP : ∀ X A : EndH, 0 ≤ P.probe (operatorFisherDiagonal (E := E) X A))
    (X A : EndH) :
    0 ≤ entropyProduction (E := E) P X A := by
  rw [entropyProduction_eq_probe_hessian (E := E) P X A]
  exact hP X A

@[rep_depth transport]
theorem thermodynamicFlux_nonneg_of_probe_hessian_nonneg
    (P : PotentialDatum (E := E))
    (hP : ∀ X A : EndH, 0 ≤ P.probe (operatorFisherDiagonal (E := E) X A))
    (X A : EndH) :
    0 ≤ thermodynamicFlux (E := E) P X A := by
  rw [thermodynamicFlux_eq_entropyProduction (E := E) P X A]
  exact entropyProduction_nonneg_of_probe_hessian_nonneg (E := E) P hP X A

end Bridge

end InfoGeometry.Canonical.Operators

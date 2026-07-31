import InfoGeometry.Canonical.SouriauModularHamiltonianBridge
import InfoGeometry.Canonical.TypeIIIContinuousCoreReal
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TypeIIISouriauCalibration

Witness-gated calibration between the bounded Souriau/Drazin modular-Hamiltonian
surrogate and the Type-III modular interface.

This file does not construct Type III modular flow from finite Souriau data.  It
only records the explicit compatibility data needed to identify the bounded
surrogate `Ksur` with the Type-III modular generator already supplied by
`TypeIIIContinuousCoreReal`.
-/

noncomputable section

namespace InfoGeometry.Canonical.TypeIIISouriauCalibration

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SouriauModularHamiltonianBridge
open InfoGeometry.Canonical.TypeIIIContinuousCoreReal

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {LieAlgebra : Type*}

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH₂" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH₂ := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH₂ := inferInstance
local instance : IsTopologicalRing EndH₂ := inferInstance
local instance : CompleteSpace EndH₂ := inferInstance
local instance : SMulCommClass ℝ EndH₂ EndH₂ := inferInstance
local instance : IsScalarTower ℝ EndH₂ EndH₂ := inferInstance

/--
Calibration packet identifying the bounded Souriau/Drazin surrogate with a
Type-III modular generator.

The exponential witness is explicit because `TypeIIIContinuousCoreReal` only
offers the Tomita `δ = log Δ` bridge after a supplied proof that
`exp(generator) = Δ`.
-/
@[rep_depth transport]
structure Calibration where
  /-- Type-III modular data owner. -/
  typeIII :
    RealTypeIIIModularData (E := E)

  /-- Finite/bounded Souriau calibration over the doubled Hilbert carrier. -/
  souriau :
    InfoGeometry.Canonical.SouriauModularHamiltonianBridge.Bridge
      (E := H₂) (LieAlgebra := LieAlgebra)

  /-- Calibration: the bounded surrogate is the Type-III modular generator. -/
  Ksur_eq_typeIII_modularGenerator :
    souriau.superBridge.Ksur = typeIII.modularGenerator

  /--
  Explicit Tomita exponential witness for the Type-III modular generator.
  This is not derived here.
  -/
  exp_typeIII_modularGenerator_eq_modularOperator :
    NormedSpace.exp typeIII.modularGenerator = typeIII.rn.modularOperator

namespace Calibration

variable (C : Calibration (E := E) (LieAlgebra := LieAlgebra))

/-- The bounded surrogate is the Type-III modular generator. -/
@[rep_depth transport]
theorem Ksur_eq_modularGenerator :
    C.souriau.superBridge.Ksur = C.typeIII.modularGenerator :=
  C.Ksur_eq_typeIII_modularGenerator

/-- The Souriau bare generator is the Type-III modular generator under calibration. -/
@[rep_depth transport]
theorem Khat_beta_eq_modularGenerator :
    C.souriau.family.Khat_beta = C.typeIII.modularGenerator := by
  calc
    C.souriau.family.Khat_beta = C.souriau.superBridge.Ksur :=
      C.souriau.Khat_beta_eq_Ksur_theorem
    _ = C.typeIII.modularGenerator :=
      C.Ksur_eq_typeIII_modularGenerator

/--
The normalized Souriau modular Hamiltonian is the Type-III modular generator
plus the Massieu/free-energy scalar identity term.
-/
@[rep_depth transport]
theorem modularHamiltonian_eq_typeIII_modularGenerator_add_partitionPotential_one :
    C.souriau.family.modularHamiltonian =
      C.typeIII.modularGenerator + C.souriau.family.partitionPotential • (1 : EndH₂) := by
  rw [C.souriau.modularHamiltonian_eq_Ksur_add_partitionPotential_one,
    C.Ksur_eq_typeIII_modularGenerator]

/-- The bounded surrogate exponentiates to the Type-III modular operator by explicit witness. -/
@[rep_depth transport]
theorem exp_Ksur_eq_modularOperator :
    NormedSpace.exp C.souriau.superBridge.Ksur = C.typeIII.rn.modularOperator := by
  rw [C.Ksur_eq_typeIII_modularGenerator]
  exact C.exp_typeIII_modularGenerator_eq_modularOperator

/-- The Souriau bare generator exponentiates to the Type-III modular operator. -/
@[rep_depth transport]
theorem exp_Khat_beta_eq_modularOperator :
    NormedSpace.exp C.souriau.family.Khat_beta = C.typeIII.rn.modularOperator := by
  rw [C.Khat_beta_eq_modularGenerator]
  exact C.exp_typeIII_modularGenerator_eq_modularOperator

/--
The bounded surrogate generates the same real Tomita flow as the calibrated
Type-III modular generator.
-/
@[rep_depth transport]
theorem Ksur_transportFlow_eq_realTomitaFlow
    (t : ℝ) :
    InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow
        (E := E) C.souriau.superBridge.Ksur t
      =
    (C.typeIII.toRealModularLogData
        C.exp_typeIII_modularGenerator_eq_modularOperator).flow t := by
  rw [C.Ksur_eq_typeIII_modularGenerator]
  exact C.typeIII.modularTransportFlow_eq_realTomitaFlow
    C.exp_typeIII_modularGenerator_eq_modularOperator t

/--
The Type-III modular generator is the RN negative-log generator supplied by the
Type-III owner lane.
-/
@[rep_depth transport]
theorem modularGenerator_eq_neg_log_rn :
    C.typeIII.modularGenerator =
      (-Real.log C.typeIII.rn.rnDerivative) •
        InfoGeometry.Canonical.YangMillsContinuum.idEndH E :=
  C.typeIII.hTypeIII.2.1

end Calibration

end Core

end InfoGeometry.Canonical.TypeIIISouriauCalibration

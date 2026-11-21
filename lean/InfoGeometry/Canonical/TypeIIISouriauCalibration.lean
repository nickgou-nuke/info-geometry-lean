/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauModularHamiltonianBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
Type-III modular generator. The Type-III exponential/logarithm identity is
derived from the positive RN scalar in `RealTypeIIIModularData`; only the
identification of the Souriau surrogate with that generator remains external.
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
  exact C.typeIII.exp_modularGenerator_eq_modularOperator

/-- The Souriau bare generator exponentiates to the Type-III modular operator. -/
@[rep_depth transport]
theorem exp_Khat_beta_eq_modularOperator :
    NormedSpace.exp C.souriau.family.Khat_beta = C.typeIII.rn.modularOperator := by
  rw [C.Khat_beta_eq_modularGenerator]
  exact C.typeIII.exp_modularGenerator_eq_modularOperator

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
    C.typeIII.toRealModularLogData.flow t := by
  rw [C.Ksur_eq_typeIII_modularGenerator]
  exact C.typeIII.modularTransportFlow_eq_realTomitaFlow t

/-- The Tomita logarithmic generator is the positive logarithm of the RN
modular scalar; the thermodynamic Hamiltonian is its negative. -/
@[rep_depth transport]
theorem modularGenerator_eq_log_rn :
    C.typeIII.modularGenerator =
      Real.log C.typeIII.rn.rnDerivative •
        InfoGeometry.Canonical.YangMillsContinuum.idEndH E :=
  C.typeIII.modularGenerator_eq_log_rn

/-- RN positivity derives the Type-III modular exponential identity; callers
no longer provide it as a compatibility witness. -/
@[rep_depth transport]
theorem exp_typeIII_modularGenerator_eq_modularOperator :
    NormedSpace.exp C.typeIII.modularGenerator = C.typeIII.rn.modularOperator :=
  C.typeIII.exp_modularGenerator_eq_modularOperator

end Calibration

end Core

end InfoGeometry.Canonical.TypeIIISouriauCalibration

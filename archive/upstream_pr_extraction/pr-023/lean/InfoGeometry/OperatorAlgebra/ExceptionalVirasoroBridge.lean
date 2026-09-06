/-
InfoGeometry/OperatorAlgebra/ExceptionalVirasoroBridge.lean

Exceptional affine/Virasoro bridge for horizon memory ledgers.

This module connects:

* five-graded hidden memory;
* horizon KMS readout;
* affine/current extension of a finite symmetry algebra;
* Virasoro stress/anomaly readout.

It does not identify finite `E8(8)` with Virasoro. The bridge is mediated by
an affine/current extension, morally `E9(9)`, and a Sugawara/stress-tensor
calibration.

The physical statement is witness-gated:

  hidden grade-two memory
      -> affine current mode
      -> Virasoro/stress central readout
      -> KMS/horizon thermal ledger.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.HorizonKMS
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ExceptionalVirasoroBridge

open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
open InfoGeometry.OperatorAlgebra.HorizonKMS
open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-! ## 1. Hidden memory as affine current data -/

/--
A calibration from five-graded horizon memory into affine current modes.

`Finite` is the finite symmetry algebra, later instantiated by a split real
exceptional algebra such as `E8(8)`.

`AffineAlg` is the affine/current algebra, later instantiated by an `E9`-type
extension.

`H` is the already-supplied horizon KMS/five-grade bridge.
-/
structure HiddenMemoryAffineCurrentCalibration
    (J L Obs Memory Finite AffineAlg : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (H : HorizonKMSFiveGradeBridge J L Obs Memory A) where

  /-- Affine/Virasoro bridge. -/
  affineVirasoro :
    AffineVirasoroBridgeDatum Finite AffineAlg

  /-- Send hidden memory into the affine/current algebra. -/
  memoryToAffine :
    Memory →ₗ[ℝ] AffineAlg

  /-- Current mode assigned to a pair of charge/state labels. -/
  modeOf :
    J → J → ℤ

  /-- Finite-algebra current label assigned to a pair of labels. -/
  finiteChargeOf :
    J → J → Finite

  /-- Hidden grade-two memory is represented by an affine current mode. -/
  hidden_memory_is_current_mode :
    ∀ x y : J,
      memoryToAffine (hiddenMemoryReadout H.ledger x y) =
        affineVirasoro.affine.Current (modeOf x y) (finiteChargeOf x y)

  /-- The finite algebra is physically interpreted as split real `E8(8)` or similar. -/
  finite_exceptional_law : Prop
  finite_exceptional_law_holds :
    finite_exceptional_law

  /-- The affine algebra is interpreted as the corresponding loop/current extension. -/
  affine_exceptional_law : Prop
  affine_exceptional_law_holds :
    affine_exceptional_law

namespace HiddenMemoryAffineCurrentCalibration

variable
    {J L Obs Memory Finite AffineAlg : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {H : HorizonKMSFiveGradeBridge J L Obs Memory A}

variable (C : HiddenMemoryAffineCurrentCalibration J L Obs Memory Finite AffineAlg H)

/-- Hidden horizon memory is represented as an affine current mode. -/
theorem memory_eq_current_mode
    (x y : J) :
    C.memoryToAffine (hiddenMemoryReadout H.ledger x y) =
      C.affineVirasoro.affine.Current (C.modeOf x y) (C.finiteChargeOf x y) :=
  C.hidden_memory_is_current_mode x y

/-- The Sugawara/stress-tensor law is available through the affine/Virasoro bridge. -/
theorem sugawara_holds :
    C.affineVirasoro.sugawara_law :=
  C.affineVirasoro.sugawara_holds

/-- The Virasoro-current reparametrization law is available through the bridge. -/
theorem virasoro_acts_on_currents :
    C.affineVirasoro.virasoro_acts_on_currents_law :=
  C.affineVirasoro.virasoro_acts_on_currents

/-- The central charge is the explicit Sugawara-calibrated value of the bridge. -/
theorem centralCharge_calibrated :
    C.affineVirasoro.centralCharge =
      C.affineVirasoro.level * C.affineVirasoro.finiteDimension /
        (C.affineVirasoro.level + C.affineVirasoro.dualCoxeterNumber) :=
  C.affineVirasoro.centralCharge_calibrated

end HiddenMemoryAffineCurrentCalibration

/-! ## 2. Virasoro central/stress readout of hidden memory -/

/--
A scalar Virasoro/stress readout of the hidden memory sector.

This is the formal socket for saying:

  hidden grade-two memory contributes to the Virasoro stress/anomaly ledger.

The readout is not automatic. It must be supplied by the representation.
-/
structure HiddenMemoryVirasoroReadout
    (J L Obs Memory Finite AffineAlg : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {H : HorizonKMSFiveGradeBridge J L Obs Memory A}
    (C : HiddenMemoryAffineCurrentCalibration J L Obs Memory Finite AffineAlg H) where

  /-- Scalar readout on affine/Virasoro algebra elements. -/
  stressScalar :
    AffineAlg →ₗ[ℝ] ℝ

  /-- Scalar readout of a memory value. -/
  memoryScalar :
    Memory →ₗ[ℝ] ℝ

  /-- Scalar boundary/stress readout of the observed three-grade defect. -/
  defectScalar :
    Obs →ₗ[ℝ] ℝ

  /-- Memory scalar agrees with stress scalar after affine-current embedding. -/
  memory_scalar_eq_stress_scalar :
    ∀ x y : J,
      memoryScalar (hiddenMemoryReadout H.ledger x y) =
        stressScalar (C.memoryToAffine (hiddenMemoryReadout H.ledger x y))

  /-- Observed defect scalar agrees with the hidden-memory scalar. -/
  defect_scalar_eq_memory_scalar :
    ∀ x y : J,
      defectScalar (A.observedDefect x y) =
        memoryScalar (hiddenMemoryReadout H.ledger x y)

  /-- Central charge / anomaly calibration law. -/
  central_anomaly_law : Prop
  central_anomaly_law_holds :
    central_anomaly_law

namespace HiddenMemoryVirasoroReadout

variable
    {J L Obs Memory Finite AffineAlg : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {H : HorizonKMSFiveGradeBridge J L Obs Memory A}
    {C : HiddenMemoryAffineCurrentCalibration J L Obs Memory Finite AffineAlg H}

variable (R : HiddenMemoryVirasoroReadout J L Obs Memory Finite AffineAlg C)

/-- Hidden memory scalar equals the affine/Virasoro stress scalar. -/
theorem hidden_memory_scalar_eq_stress_scalar
    (x y : J) :
    R.memoryScalar (hiddenMemoryReadout H.ledger x y) =
      R.stressScalar (C.memoryToAffine (hiddenMemoryReadout H.ledger x y)) :=
  R.memory_scalar_eq_stress_scalar x y

/-- Observed defect scalar equals the hidden-memory scalar. -/
theorem observed_defect_scalar_eq_hidden_memory_scalar
    (x y : J) :
    R.defectScalar (A.observedDefect x y) =
      R.memoryScalar (hiddenMemoryReadout H.ledger x y) :=
  R.defect_scalar_eq_memory_scalar x y

/- The observed hidden projection has the same scalar readout as hidden memory. -/
theorem observed_hidden_projection_scalar_eq_hidden_memory_scalar
    (x y : J) :
    R.defectScalar (visibleHiddenProjection H.ledger x y) =
      R.memoryScalar (hiddenMemoryReadout H.ledger x y) := by
  rw [← observedDefect_eq_visibleHiddenProjection H.ledger x y]
  exact R.observed_defect_scalar_eq_hidden_memory_scalar x y

/--
After rewriting hidden memory as a current mode, the memory scalar is the stress
readout of that affine current mode.
-/
theorem hidden_memory_scalar_eq_current_stress
    (x y : J) :
    R.memoryScalar (hiddenMemoryReadout H.ledger x y) =
      R.stressScalar
        (C.affineVirasoro.affine.Current (C.modeOf x y) (C.finiteChargeOf x y)) := by
  rw [R.hidden_memory_scalar_eq_stress_scalar x y]
  rw [C.memory_eq_current_mode x y]

/--
The observed defect scalar equals the affine/Virasoro stress readout of the
hidden grade-two current mode.
-/
theorem observed_defect_scalar_eq_current_stress
    (x y : J) :
    R.defectScalar (A.observedDefect x y) =
      R.stressScalar
        (C.affineVirasoro.affine.Current (C.modeOf x y) (C.finiteChargeOf x y)) := by
  rw [R.observed_defect_scalar_eq_hidden_memory_scalar x y]
  exact R.hidden_memory_scalar_eq_current_stress x y

/--
Equivalent form using the observer's hidden projection theorem.
-/
theorem observed_hidden_projection_scalar_eq_current_stress
    (x y : J) :
    R.defectScalar (visibleHiddenProjection H.ledger x y) =
      R.stressScalar
        (C.affineVirasoro.affine.Current (C.modeOf x y) (C.finiteChargeOf x y)) := by
  rw [← observedDefect_eq_visibleHiddenProjection H.ledger x y]
  exact R.observed_defect_scalar_eq_current_stress x y

/-- The installed central anomaly law is available. -/
theorem central_anomaly :
    R.central_anomaly_law :=
  R.central_anomaly_law_holds

end HiddenMemoryVirasoroReadout

/-! ## 3. Horizon KMS + Virasoro bridge -/

/--
Combined horizon KMS and exceptional affine/Virasoro bridge.

This is the exact socket for:

  hidden grade-two memory
      -> affine current mode
      -> Virasoro stress/anomaly scalar
      -> KMS/horizon thermal observer readout.
-/
structure HorizonExceptionalVirasoroBridge
    (J L Obs Memory Finite AffineAlg : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    {G : FiveGrading L}
    (A : FiveGradeProjectedAccounting J L Obs G) where

  /-- Horizon KMS/five-grade ledger. -/
  horizon :
    HorizonKMSFiveGradeBridge J L Obs Memory A

  /-- Hidden memory to affine current calibration. -/
  currentCalibration :
    HiddenMemoryAffineCurrentCalibration J L Obs Memory Finite AffineAlg horizon

  /-- Virasoro/stress readout of hidden memory. -/
  virasoroReadout :
    HiddenMemoryVirasoroReadout J L Obs Memory Finite AffineAlg currentCalibration

  /-- Law saying the KMS thermal flux readout is calibrated by Virasoro stress/anomaly. -/
  kms_flux_eq_virasoro_stress_law : Prop
  kms_flux_eq_virasoro_stress_law_holds :
    kms_flux_eq_virasoro_stress_law

  /-- Law saying the affine/Virasoro central charge is the boundary version of memory. -/
  central_charge_is_grade_two_memory_law : Prop
  central_charge_is_grade_two_memory_law_holds :
    central_charge_is_grade_two_memory_law

namespace HorizonExceptionalVirasoroBridge

variable
    {J L Obs Memory Finite AffineAlg : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}

variable (B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A)

/-- The exterior observer carries the installed KMS boundary law. -/
theorem observer_has_kms_boundary :
    B.horizon.kms.kms_boundary_law :=
  B.horizon.kms.kms_boundary_certificate

/-- The observed defect is the visible projection of hidden grade-two memory. -/
theorem observed_defect_is_hidden_projection
    (x y : J) :
    A.observedDefect x y = visibleHiddenProjection B.horizon.ledger x y :=
  observedDefect_eq_visibleHiddenProjection B.horizon.ledger x y

/-- Hidden grade-two memory is represented by an affine current mode. -/
theorem hidden_memory_eq_current_mode
    (x y : J) :
    B.currentCalibration.memoryToAffine
        (hiddenMemoryReadout B.horizon.ledger x y) =
      B.currentCalibration.affineVirasoro.affine.Current
        (B.currentCalibration.modeOf x y)
        (B.currentCalibration.finiteChargeOf x y) :=
  B.currentCalibration.memory_eq_current_mode x y

/-- The scalar hidden memory readout equals the scalar Virasoro/current stress readout. -/
theorem hidden_memory_scalar_eq_current_stress
    (x y : J) :
    B.virasoroReadout.memoryScalar
        (hiddenMemoryReadout B.horizon.ledger x y) =
      B.virasoroReadout.stressScalar
        (B.currentCalibration.affineVirasoro.affine.Current
          (B.currentCalibration.modeOf x y)
          (B.currentCalibration.finiteChargeOf x y)) :=
  B.virasoroReadout.hidden_memory_scalar_eq_current_stress x y

/--
The observed defect scalar equals the Virasoro/current stress readout of hidden
grade-two memory.
-/
theorem observed_defect_scalar_eq_current_stress
    (x y : J) :
    B.virasoroReadout.defectScalar (A.observedDefect x y) =
      B.virasoroReadout.stressScalar
        (B.currentCalibration.affineVirasoro.affine.Current
          (B.currentCalibration.modeOf x y)
          (B.currentCalibration.finiteChargeOf x y)) :=
  B.virasoroReadout.observed_defect_scalar_eq_current_stress x y

/--
Equivalent form using the visible hidden projection supplied by the five-grade
ledger.
-/
theorem observed_hidden_projection_scalar_eq_current_stress
    (x y : J) :
    B.virasoroReadout.defectScalar (visibleHiddenProjection B.horizon.ledger x y) =
      B.virasoroReadout.stressScalar
        (B.currentCalibration.affineVirasoro.affine.Current
          (B.currentCalibration.modeOf x y)
          (B.currentCalibration.finiteChargeOf x y)) :=
  B.virasoroReadout.observed_hidden_projection_scalar_eq_current_stress x y

/-- The Sugawara/stress-tensor law is available in the bridge. -/
theorem sugawara_holds :
    B.currentCalibration.affineVirasoro.sugawara_law :=
  B.currentCalibration.sugawara_holds

/-- The Virasoro-current reparametrization law is available in the bridge. -/
theorem virasoro_acts_on_currents :
    B.currentCalibration.affineVirasoro.virasoro_acts_on_currents_law :=
  B.currentCalibration.virasoro_acts_on_currents

/-- The installed KMS/Virasoro flux law is available. -/
theorem kms_flux_eq_virasoro_stress :
    B.kms_flux_eq_virasoro_stress_law :=
  B.kms_flux_eq_virasoro_stress_law_holds

/-- The installed central-charge/memory law is available. -/
theorem central_charge_is_grade_two_memory :
    B.central_charge_is_grade_two_memory_law :=
  B.central_charge_is_grade_two_memory_law_holds

end HorizonExceptionalVirasoroBridge

/-! ## 4. Central/stress charge readout -/

/--
Generic central/stress charge readout of hidden memory.

This is the boundary-accounting form of the bridge: the affine/Virasoro
central or stress readout of a hidden-memory event equals the hidden grade-two
memory readout.
-/
structure HiddenMemoryCentralChargeReadout
    (J L Obs Memory Finite AffineAlg Charge : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {H : HorizonKMSFiveGradeBridge J L Obs Memory A}
    (C : HiddenMemoryAffineCurrentCalibration J L Obs Memory Finite AffineAlg H) where

  /-- Charge/readout of an affine/Virasoro central or stress element. -/
  centralReadout :
    AffineAlg →ₗ[ℝ] Charge

  /-- Charge/readout of hidden grade-two memory. -/
  hiddenMemoryChargeReadout :
    Memory →ₗ[ℝ] Charge

  /-- Central/stress readout equals hidden grade-two memory readout. -/
  central_equals_hidden_memory :
    ∀ x y : J,
      centralReadout
          (C.affineVirasoro.affine.Current (C.modeOf x y) (C.finiteChargeOf x y))
        =
      hiddenMemoryChargeReadout (hiddenMemoryReadout H.ledger x y)

  /--
  Boundary interpretation certificate.

  This is where a concrete model says the affine/Virasoro element is the
  intended stress tensor, central anomaly, or boundary helical readout.
  -/
  boundary_stress_interpretation_law : Prop
  boundary_stress_interpretation_certificate :
    boundary_stress_interpretation_law

namespace HiddenMemoryCentralChargeReadout

variable
    {J L Obs Memory Finite AffineAlg Charge : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {H : HorizonKMSFiveGradeBridge J L Obs Memory A}
    {C : HiddenMemoryAffineCurrentCalibration J L Obs Memory Finite AffineAlg H}

variable (R : HiddenMemoryCentralChargeReadout J L Obs Memory Finite AffineAlg Charge C)

/- The affine/Virasoro central/stress readout equals hidden grade-two memory readout. -/
theorem central_readout_eq_hidden_memory_readout
    (x y : J) :
    R.centralReadout
        (C.affineVirasoro.affine.Current (C.modeOf x y) (C.finiteChargeOf x y))
      =
    R.hiddenMemoryChargeReadout (hiddenMemoryReadout H.ledger x y) :=
  R.central_equals_hidden_memory x y

/- Equivalent form after expanding the hidden memory as its affine current mode. -/
theorem central_readout_eq_hidden_memory_readout_of_current
    (x y : J) :
    R.centralReadout
        (C.memoryToAffine (hiddenMemoryReadout H.ledger x y))
      =
    R.hiddenMemoryChargeReadout (hiddenMemoryReadout H.ledger x y) := by
  rw [C.memory_eq_current_mode x y]
  exact R.central_readout_eq_hidden_memory_readout x y

/- The installed boundary stress interpretation law is available. -/
theorem boundary_stress_interpretation :
    R.boundary_stress_interpretation_law :=
  R.boundary_stress_interpretation_certificate

end HiddenMemoryCentralChargeReadout

/-! ## 5. KMS / Virasoro charge compatibility -/

/--
Compatibility between horizon KMS defect readout and affine/Virasoro central
or stress readout.

This states that the observer's thermal/defect charge, the Virasoro boundary
charge, and the hidden grade-two memory charge are calibrated to the same
quantity.
-/
structure HorizonKMSVirasoroChargeCompatibility
    (J L Obs Memory Finite AffineAlg Charge : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A) where

  /-- Central/stress charge bridge for the same hidden current calibration. -/
  centralChargeReadout :
    HiddenMemoryCentralChargeReadout
      J L Obs Memory Finite AffineAlg Charge B.currentCalibration

  /-- KMS/thermal charge readout of the exterior observed defect. -/
  kmsChargeReadout :
    Obs →ₗ[ℝ] Charge

  /--
  The KMS readout of the observed defect agrees with the affine/Virasoro
  central readout of the hidden memory.
  -/
  kms_defect_eq_virasoro_central :
    ∀ x y : J,
      kmsChargeReadout (A.observedDefect x y)
        =
      centralChargeReadout.centralReadout
        (B.currentCalibration.affineVirasoro.affine.Current
          (B.currentCalibration.modeOf x y)
          (B.currentCalibration.finiteChargeOf x y))

namespace HorizonKMSVirasoroChargeCompatibility

variable
    {J L Obs Memory Finite AffineAlg Charge : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg]
    [AddCommGroup Charge] [Module ℝ Charge]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A}

variable (K : HorizonKMSVirasoroChargeCompatibility J L Obs Memory Finite AffineAlg Charge B)

/- KMS defect readout equals affine/Virasoro central/stress readout. -/
theorem kms_readout_eq_virasoro_central
    (x y : J) :
    K.kmsChargeReadout (A.observedDefect x y)
      =
    K.centralChargeReadout.centralReadout
      (B.currentCalibration.affineVirasoro.affine.Current
        (B.currentCalibration.modeOf x y)
        (B.currentCalibration.finiteChargeOf x y)) :=
  K.kms_defect_eq_virasoro_central x y

/- The KMS defect readout is also the hidden grade-two memory readout. -/
theorem kms_readout_eq_hidden_memory
    (x y : J) :
    K.kmsChargeReadout (A.observedDefect x y)
      =
    K.centralChargeReadout.hiddenMemoryChargeReadout
      (hiddenMemoryReadout B.horizon.ledger x y) := by
  rw [K.kms_readout_eq_virasoro_central x y]
  exact K.centralChargeReadout.central_readout_eq_hidden_memory_readout x y

end HorizonKMSVirasoroChargeCompatibility

/-! ## 6. Virasoro anomaly coefficient on global modes -/

/--
The Virasoro anomaly coefficient `m(m² - 1)` vanishes on the global conformal
modes `m = -1, 0, 1`.

This is the algebraic reason the global `sl₂` conformal subalgebra is
anomaly-free while higher local modes may carry central charge.
-/
theorem virasoro_anomalyCoeff_zero_on_global_modes
    (m : ℤ)
    (hm : m = -1 ∨ m = 0 ∨ m = 1) :
    m * (m ^ 2 - 1) = 0 :=
  virasoroCentralPolynomial_global_zero m hm

/-! ## 7. Owner target -/

/--
Owner target for the exceptional affine/Virasoro horizon bridge.

Once the bridge is supplied:

* the observer carries a KMS boundary law;
* hidden grade-two memory is represented as an affine current;
* the hidden memory scalar equals the Virasoro/current stress readout.
-/
@[owner_target_tag]
def ExceptionalVirasoroBridgeOwnerTarget : Prop :=
  ∀ (J L Obs Memory Finite AffineAlg : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup AffineAlg] [Module ℝ AffineAlg]
    [LieRing AffineAlg] [LieAlgebra ℝ AffineAlg],
  ∀ G : FiveGrading L,
  ∀ A : FiveGradeProjectedAccounting J L Obs G,
  ∀ B : HorizonExceptionalVirasoroBridge J L Obs Memory Finite AffineAlg A,
    B.horizon.kms.kms_boundary_law ∧
    (∀ x y : J,
      B.currentCalibration.memoryToAffine
          (hiddenMemoryReadout B.horizon.ledger x y) =
        B.currentCalibration.affineVirasoro.affine.Current
          (B.currentCalibration.modeOf x y)
          (B.currentCalibration.finiteChargeOf x y))

/-- The owner target follows from the supplied exceptional/Virasoro bridge. -/
theorem exceptionalVirasoroBridgeOwnerTarget :
    ExceptionalVirasoroBridgeOwnerTarget := by
  intro J L Obs Memory Finite AffineAlg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G A B
  exact ⟨B.observer_has_kms_boundary, fun x y => B.hidden_memory_eq_current_mode x y⟩

end InfoGeometry.OperatorAlgebra.ExceptionalVirasoroBridge

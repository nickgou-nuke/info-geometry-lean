/-
InfoGeometry/OperatorAlgebra/HorizonKMS.lean

Horizon KMS readout from five-graded information memory.

This module connects:

  * five-graded hidden memory;
  * three-grade observer projection;
  * modular/KMS readout for the exterior observer;
  * optional horizon/boost temperature normalization.

It does not claim that `E8`, a five-grading, or a Clifford algebra alone proves
Hawking radiation. The KMS and horizon/boost identifications are separate
theorem-level obligations, and recovery/Page-curve/holographic reconstruction
statements remain separate property structures.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.OperatorAlgebra.TomitaCartanSplit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.HorizonKMS

open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics
open InfoGeometry.OperatorAlgebra.Thermodynamics
open InfoGeometry.OperatorAlgebra.TomitaCartanSplit

/-! ## 1. Modular KMS readout socket -/

/--
A KMS readout datum for a modular or horizon flow.

This is not a full algebraic KMS state unless the observable product,
positivity, normalization, and analytic strip law are supplied by a concrete
model.
-/
structure KMSReadoutDatum
    (Obs : Type*) [AddCommGroup Obs] [Module ℝ Obs] where
  /-- Modular/horizon flow on observable data. -/
  flow : ℝ → Obs → Obs

  /-- State or weight readout. -/
  state : Obs → ℝ

  /-- Inverse temperature. -/
  beta : ℝ

  /-- Positive inverse temperature. -/
  beta_pos : 0 < beta

  /-- Zero-time flow law. -/
  flow_zero :
    ∀ x : Obs, flow 0 x = x

  /-- Additive flow law. -/
  flow_add :
    ∀ s t x, flow (s + t) x = flow s (flow t x)

  /-- State is invariant under the real modular flow. -/
  flow_invariant :
    ∀ t x, state (flow t x) = state x

namespace KMSReadoutDatum

variable
    {Obs : Type*} [AddCommGroup Obs] [Module ℝ Obs]

variable (K : KMSReadoutDatum Obs)

/-- Re-export flow invariance. -/
theorem invariant
    (t : ℝ)
    (x : Obs) :
    K.state (K.flow t x) = K.state x :=
  K.flow_invariant t x

/-- The inverse temperature is nonzero. -/
theorem beta_ne_zero :
    K.beta ≠ 0 :=
  ne_of_gt K.beta_pos

/-- Re-export zero-time flow. -/
theorem flow_zero_apply
    (x : Obs) :
    K.flow 0 x = x :=
  K.flow_zero x

/-- Re-export additive flow law. -/
theorem flow_add_apply
    (s t : ℝ)
    (x : Obs) :
    K.flow (s + t) x = K.flow s (K.flow t x) :=
  K.flow_add s t x

end KMSReadoutDatum

/--
Backward-compatible alias.

Prefer `KMSReadoutDatum` in new code. This alias exists so older modules that
refer to `KMSStateDatum` do not need to be migrated immediately.
-/
abbrev KMSStateDatum
    (Obs : Type*) [AddCommGroup Obs] [Module ℝ Obs] :=
  KMSReadoutDatum Obs

namespace KMSStateDatum

variable
    {Obs : Type*} [AddCommGroup Obs] [Module ℝ Obs]

variable (K : KMSStateDatum Obs)

/-- Compatibility alias for `KMSReadoutDatum.invariant`. -/
theorem invariant
    (t : ℝ)
    (x : Obs) :
    K.state (K.flow t x) = K.state x :=
  KMSReadoutDatum.invariant K t x

/-- Compatibility alias for `KMSReadoutDatum.beta_ne_zero`. -/
theorem beta_ne_zero :
    K.beta ≠ 0 :=
  KMSReadoutDatum.beta_ne_zero K

/-- Compatibility alias for `KMSReadoutDatum.flow_zero_apply`. -/
theorem flow_zero_apply
    (x : Obs) :
    K.flow 0 x = x :=
  KMSReadoutDatum.flow_zero_apply K x

/-- Compatibility alias for `KMSReadoutDatum.flow_add_apply`. -/
theorem flow_add_apply
    (s t : ℝ)
    (x : Obs) :
    K.flow (s + t) x = K.flow s (K.flow t x) :=
  KMSReadoutDatum.flow_add_apply K s t x

end KMSStateDatum

/-! ## 2. Horizon temperature normalization -/

/--
Horizon modular temperature normalization.

`surfaceGravity` may be read as acceleration in the Unruh case or surface
gravity in the black-hole/Hawking case. Natural units are used:

`β = 2π / κ`, hence `T = κ / 2π`.
-/
structure HorizonKMSNormalization where
  /-- Acceleration or surface gravity. -/
  surfaceGravity : ℝ

  /-- Positive acceleration/surface gravity. -/
  surfaceGravity_pos :
    0 < surfaceGravity

  /-- Inverse temperature. -/
  beta : ℝ

  /-- Temperature. -/
  temperature : ℝ

  /--
  Modular/horizon normalization.

  Natural units: `β = 2π / κ`.
  -/
  beta_eq_two_pi_over_surfaceGravity :
    beta = (2 * Real.pi) / surfaceGravity

  /--
  Natural-unit temperature law.

  `T = κ / 2π`.
  -/
  temperature_eq_surfaceGravity_over_two_pi :
    temperature = surfaceGravity / (2 * Real.pi)

  /--
  Explicit horizon-modular calibration law.

  Natural units: `β * κ = 2π`.
  -/
  horizon_modular_calibration :
    beta * surfaceGravity = 2 * Real.pi

namespace HorizonKMSNormalization

variable (N : HorizonKMSNormalization)

/-- The calibrated inverse temperature is positive. -/
theorem beta_pos :
    0 < N.beta := by
  rw [N.beta_eq_two_pi_over_surfaceGravity]
  exact div_pos (by positivity : 0 < (2 * Real.pi : ℝ)) N.surfaceGravity_pos

/-- The calibrated natural-unit temperature is positive. -/
theorem temperature_pos :
    0 < N.temperature := by
  rw [N.temperature_eq_surfaceGravity_over_two_pi]
  exact div_pos N.surfaceGravity_pos (by positivity : 0 < (2 * Real.pi : ℝ))

/-- Natural-unit inverse temperature and temperature multiply to one. -/
theorem beta_mul_temperature_eq_one :
    N.beta * N.temperature = 1 := by
  rw [
    N.beta_eq_two_pi_over_surfaceGravity,
    N.temperature_eq_surfaceGravity_over_two_pi
  ]
  have hκ : N.surfaceGravity ≠ 0 :=
    ne_of_gt N.surfaceGravity_pos
  have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hκ, h2π]

/-- Temperature and inverse temperature multiply to one. -/
theorem temperature_mul_beta_eq_one :
    N.temperature * N.beta = 1 := by
  rw [mul_comm]
  exact N.beta_mul_temperature_eq_one

/-- The calibrated inverse temperature is nonzero. -/
theorem beta_ne_zero :
    N.beta ≠ 0 :=
  ne_of_gt N.beta_pos

/-- The calibrated temperature is nonzero. -/
theorem temperature_ne_zero :
    N.temperature ≠ 0 :=
  ne_of_gt N.temperature_pos

/-- Re-export the explicit horizon-modular calibration law. -/
theorem horizon_modular_calibration_eq :
    N.beta * N.surfaceGravity = 2 * Real.pi :=
  N.horizon_modular_calibration

end HorizonKMSNormalization

/-! ## 3. Hidden grade-two memory projection -/

/-- Hidden grade-two memory element of a black-hole information ledger. -/
def hiddenGradeTwoSum
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (_B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) : L :=
  A.hiddenTotal x y

/-- Memory readout of the hidden grade-two sector. -/
def hiddenMemoryReadout
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) : Memory :=
  B.memoryReadout (hiddenGradeTwoSum B x y)

/-- Observable projection of the hidden grade-two sector. -/
def visibleHiddenProjection
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) : Obs :=
  A.obs (hiddenGradeTwoSum B x y)

/-- The observed defect equals the observable projection of hidden grade-two memory. -/
theorem observedDefect_eq_visibleHiddenProjection
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) :
    A.observedDefect x y =
      visibleHiddenProjection B x y := by
  dsimp [visibleHiddenProjection, hiddenGradeTwoSum]
  exact A.observedDefect_eq_obs_hidden x y

/--
The observer sees a nonzero defect iff the hidden grade-two projection is
nonzero.
-/
theorem observedDefect_ne_zero_iff_visibleHidden_ne_zero
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : BlackHoleInformationLedger J L Obs Memory A)
    (x y : J) :
    A.observedDefect x y ≠ 0 ↔
      visibleHiddenProjection B x y ≠ 0 := by
  rw [observedDefect_eq_visibleHiddenProjection B x y]

/-! ## 4. Hidden grade-two memory heat -/

/--
Grade-two hidden memory heat calibration.

This says that the observed exterior heat/defect readout is exactly the heat
stored in the hidden `g₋₂ ⊕ g₊₂` memory sector.
-/
structure GradeTwoMemoryHeatCalibration
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : BlackHoleInformationLedger J L Obs Memory A) where

  /-- Observed thermal/defect heat readout. -/
  observedHeat : Obs → ℝ

  /-- Hidden memory energy/heat readout. -/
  memoryHeat : Memory → ℝ

  /--
  Heat accounting law.

  The observed heat of the three-grade defect equals the hidden memory heat of
  the total grade-two sector.
  -/
  observed_heat_eq_gradeTwo_memory_heat :
    ∀ x y : J,
      observedHeat (A.observedDefect x y) =
        memoryHeat (B.memoryReadout (A.hiddenTotal x y))

namespace GradeTwoMemoryHeatCalibration

variable
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {B : BlackHoleInformationLedger J L Obs Memory A}

variable (H : GradeTwoMemoryHeatCalibration J L Obs Memory B)

/-- Re-export: observed defect heat equals hidden grade-two memory heat. -/
theorem observed_heat_eq_memory_heat
    (x y : J) :
    H.observedHeat (A.observedDefect x y) =
      H.memoryHeat (B.memoryReadout (A.hiddenTotal x y)) :=
  H.observed_heat_eq_gradeTwo_memory_heat x y

/--
Observed defect heat vanishes iff hidden grade-two memory heat vanishes.
-/
theorem observed_heat_eq_zero_iff_memory_heat_eq_zero
    (x y : J) :
    H.observedHeat (A.observedDefect x y) = 0 ↔
      H.memoryHeat (B.memoryReadout (A.hiddenTotal x y)) = 0 := by
  rw [H.observed_heat_eq_memory_heat x y]

/--
Observed defect heat is nonzero iff hidden grade-two memory heat is nonzero.
-/
theorem observed_heat_ne_zero_iff_memory_heat_ne_zero
    (x y : J) :
    H.observedHeat (A.observedDefect x y) ≠ 0 ↔
      H.memoryHeat (B.memoryReadout (A.hiddenTotal x y)) ≠ 0 := by
  rw [H.observed_heat_eq_memory_heat x y]

end GradeTwoMemoryHeatCalibration

/-! ## 5. Horizon KMS / five-grade bridge -/

/--
Horizon KMS bridge for a five-grade information ledger.

This packages:

* exterior KMS thermality;
* horizon temperature normalization;
* grade-two memory heat accounting.

It does not assert full recovery of information. Recovery is represented by
the separate grade-two memory recovery structure below.
-/
structure HorizonKMSFiveGradeBridge
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    (A : FiveGradeProjectedAccounting J L Obs G) where

  /-- Five-grade black-hole information ledger. -/
  ledger :
    BlackHoleInformationLedger J L Obs Memory A

  /-- Exterior KMS state/readout. -/
  kms :
    KMSReadoutDatum Obs

  /-- Horizon/Unruh/Hawking temperature normalization. -/
  normalization :
    HorizonKMSNormalization

  /-- Hidden grade-two memory heat calibration. -/
  heatCalibration :
    GradeTwoMemoryHeatCalibration J L Obs Memory ledger

  /--
  Temperature compatibility.

  The KMS inverse temperature agrees with the horizon normalization.
  -/
  kms_beta_eq_horizon_beta :
    kms.beta = normalization.beta



namespace HorizonKMSFiveGradeBridge

variable
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}

variable (H : HorizonKMSFiveGradeBridge J L Obs Memory A)

/--
The exterior KMS inverse temperature equals the horizon-normalized inverse
temperature.
-/
theorem beta_eq_horizon_beta :
    H.kms.beta = H.normalization.beta :=
  H.kms_beta_eq_horizon_beta

/-- The horizon-normalized KMS inverse temperature is positive. -/
theorem kms_beta_pos :
    0 < H.kms.beta := by
  rw [H.beta_eq_horizon_beta]
  exact H.normalization.beta_pos

/-- The KMS inverse temperature is nonzero. -/
theorem kms_beta_ne_zero :
    H.kms.beta ≠ 0 :=
  ne_of_gt H.kms_beta_pos

/-- The horizon-normalized temperature is positive. -/
theorem horizon_temperature_pos :
    0 < H.normalization.temperature :=
  H.normalization.temperature_pos

/-- The horizon-normalized temperature is nonzero. -/
theorem horizon_temperature_ne_zero :
    H.normalization.temperature ≠ 0 :=
  ne_of_gt H.horizon_temperature_pos

/-- KMS inverse temperature times horizon temperature is one. -/
theorem kms_beta_mul_horizon_temperature_eq_one :
    H.kms.beta * H.normalization.temperature = 1 := by
  rw [H.beta_eq_horizon_beta]
  exact H.normalization.beta_mul_temperature_eq_one

/-- The horizon temperature is `κ / 2π` in natural units. -/
theorem temperature_eq_surfaceGravity_over_two_pi :
    H.normalization.temperature =
      H.normalization.surfaceGravity / (2 * Real.pi) :=
  H.normalization.temperature_eq_surfaceGravity_over_two_pi

/-- The horizon inverse temperature is `2π / κ` in natural units. -/
theorem beta_eq_two_pi_div_surfaceGravity :
    H.kms.beta =
      (2 * Real.pi) / H.normalization.surfaceGravity := by
  rw [H.beta_eq_horizon_beta]
  exact H.normalization.beta_eq_two_pi_over_surfaceGravity

/-- Alias using the common division naming convention. -/
theorem temperature_eq_surfaceGravity_div_two_pi :
    H.normalization.temperature =
      H.normalization.surfaceGravity / (2 * Real.pi) :=
  H.temperature_eq_surfaceGravity_over_two_pi

/-- Observed horizon heat equals hidden grade-two memory heat. -/
theorem observed_heat_eq_gradeTwo_memory_heat
    (x y : J) :
    H.heatCalibration.observedHeat (A.observedDefect x y) =
      H.heatCalibration.memoryHeat (H.ledger.memoryReadout (A.hiddenTotal x y)) :=
  H.heatCalibration.observed_heat_eq_memory_heat x y

/--
Observed thermal heat is zero iff hidden grade-two memory heat is zero.
-/
theorem observed_heat_eq_zero_iff_gradeTwo_memory_heat_eq_zero
    (x y : J) :
    H.heatCalibration.observedHeat (A.observedDefect x y) = 0 ↔
      H.heatCalibration.memoryHeat
        (H.ledger.memoryReadout (A.hiddenTotal x y)) = 0 := by
  rw [H.observed_heat_eq_gradeTwo_memory_heat x y]

/--
Observed thermal heat is nonzero iff hidden grade-two memory heat is nonzero.
-/
theorem observed_heat_ne_zero_iff_gradeTwo_memory_heat_ne_zero
    (x y : J) :
    H.heatCalibration.observedHeat (A.observedDefect x y) ≠ 0 ↔
      H.heatCalibration.memoryHeat
        (H.ledger.memoryReadout (A.hiddenTotal x y)) ≠ 0 := by
  rw [H.observed_heat_eq_gradeTwo_memory_heat x y]

/--
If the hidden grade-two sector has nonzero memory heat, the corresponding
observed thermal heat readout is nonzero.
-/
theorem nonzero_memory_heat_readout
    {x y : J}
    (hmem :
      H.heatCalibration.memoryHeat
        (H.ledger.memoryReadout (A.hiddenTotal x y)) ≠ 0) :
    H.heatCalibration.observedHeat (A.observedDefect x y) ≠ 0 :=
  (H.observed_heat_ne_zero_iff_gradeTwo_memory_heat_ne_zero x y).mpr hmem

/--
The bridge preserves the lower ledger's property memory-storage implication.

This is intentionally weaker than a Page-curve or holographic recovery theorem:
the five-graded ledger only proves that nonzero memory readout stores a
nonzero hidden grade-two component.
-/
theorem full_ledger_recovery_holds :
    ∀ x y : J,
      H.ledger.memoryReadout (A.hiddenTotal x y) ≠ 0 →
        A.hiddenTotal x y ≠ 0 :=
  H.ledger.hidden_part_stored_as_memory

/--
Exterior KMS flow calibration as an explicit equation.

This is the local equation-level replacement for the removed
`exterior_kms_flow_calibration` property: the KMS flow supplied by the bridge is
identified with a designated horizon modular flow.
-/
def exterior_kms_flow_calibration
    (modularFlow_horizon : ℝ → Obs → Obs) : Prop :=
  ∀ t : ℝ, ∀ X : Obs, H.kms.flow t X = modularFlow_horizon t X

/-- Re-export of the exterior KMS/horizon modular flow equation. -/
theorem exterior_kms_flow_calibration_at
    {modularFlow_horizon : ℝ → Obs → Obs}
    (hcal : H.exterior_kms_flow_calibration modularFlow_horizon)
    (t : ℝ)
    (X : Obs) :
    H.kms.flow t X = modularFlow_horizon t X :=
  hcal t X

/--
Grade-two memory source law: hidden total lies in the ±2 graded sectors.

This reinstates the old horizon-source intent using explicit membership in the
five-grading sum `gNegTwo ⊔ gPosTwo`.
-/
theorem grade_two_memory_is_horizon_source
    (x y : J) :
    A.hiddenTotal x y ∈ G.gNegTwo ⊔ G.gPosTwo := by
  dsimp [FiveGradeProjectedAccounting.hiddenTotal]
  exact Submodule.add_mem_sup (A.hiddenNegTwo_mem x y) (A.hiddenPosTwo_mem x y)

end HorizonKMSFiveGradeBridge

/-! ## 6. KMS event readout -/

/--
A scalar KMS event readout over an installed horizon/five-grade bridge.

The event observable lives in the exterior observable space `Obs`, so the KMS
state supplied by the bridge can evaluate it directly.
-/
structure GradeTwoKMSThermalReadout
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (H : HorizonKMSFiveGradeBridge J L Obs Memory A) where

  /-- Observable representing a charge-pair/horizon event. -/
  eventObservable : J → J → Obs

  /-- Scalar readout of the observed three-grade defect. -/
  defectScalar : Obs → ℝ

  /-- Scalar readout of the hidden grade-two memory. -/
  memoryScalar : Memory → ℝ

  /--
  Hidden grade-two memory and observed three-grade defect have the same scalar
  readout.
  -/
  memoryScalar_eq_defectScalar :
    ∀ x y : J,
      memoryScalar (H.ledger.memoryReadout (A.hiddenTotal x y)) =
        defectScalar (A.observedDefect x y)

  /-- The KMS expectation of the event observable reads hidden memory. -/
  kms_reads_hidden_memory :
    ∀ x y : J,
      H.kms.state (eventObservable x y) =
        memoryScalar (H.ledger.memoryReadout (A.hiddenTotal x y))

namespace GradeTwoKMSThermalReadout

variable
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {H : HorizonKMSFiveGradeBridge J L Obs Memory A}

variable (R : GradeTwoKMSThermalReadout J L Obs Memory H)

/-- The KMS event expectation equals the hidden grade-two memory readout. -/
theorem kms_event_eq_hidden_memory
    (x y : J) :
    H.kms.state (R.eventObservable x y) =
      R.memoryScalar (H.ledger.memoryReadout (A.hiddenTotal x y)) :=
  R.kms_reads_hidden_memory x y

/--
The KMS event expectation equals the scalar readout of the observed
three-grade defect.
-/
theorem kms_event_eq_observed_defect
    (x y : J) :
    H.kms.state (R.eventObservable x y) =
      R.defectScalar (A.observedDefect x y) := by
  rw [R.kms_event_eq_hidden_memory x y]
  exact R.memoryScalar_eq_defectScalar x y

/--
Nonzero observed defect scalar implies nonzero KMS event expectation.
-/
theorem kms_event_ne_zero_of_observed_defect_ne_zero
    {x y : J}
    (h : R.defectScalar (A.observedDefect x y) ≠ 0) :
    H.kms.state (R.eventObservable x y) ≠ 0 := by
  rw [R.kms_event_eq_observed_defect x y]
  exact h

/--
Nonzero hidden memory scalar implies nonzero KMS event expectation.
-/
theorem kms_event_ne_zero_of_hidden_memory_ne_zero
    {x y : J}
    (h :
      R.memoryScalar
        (H.ledger.memoryReadout (A.hiddenTotal x y)) ≠ 0) :
    H.kms.state (R.eventObservable x y) ≠ 0 := by
  rw [R.kms_event_eq_hidden_memory x y]
  exact h

/-- The KMS state is invariant under real modular time. -/
theorem kms_flow_invariant
    (t : ℝ)
    (X : Obs) :
    H.kms.state (H.kms.flow t X) = H.kms.state X :=
  H.kms.invariant t X

end GradeTwoKMSThermalReadout

/-! ## 7. Recovery remains separate -/

/--
Certified recovery data for grade-two horizon memory.

This is deliberately separated from the KMS bridge. KMS thermality tells us
what the exterior observer thermally reads; recovery tells us how the hidden
memory can be reconstructed in a full model.
-/
structure GradeTwoMemoryRecoveryData
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (B : BlackHoleInformationLedger J L Obs Memory A) where

  /-- Exterior observable reconstruction data. -/
  exteriorData : Obs → Memory

  /-- Exact recovery law from observed defect to hidden grade-two memory. -/
  recover_hidden_memory_law :
    ∀ x y : J,
      exteriorData (A.observedDefect x y) =
        B.memoryReadout (A.hiddenTotal x y)

namespace GradeTwoMemoryRecoveryData

variable
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {B : BlackHoleInformationLedger J L Obs Memory A}

variable (R : GradeTwoMemoryRecoveryData J L Obs Memory B)

/-- Hidden memory is recoverable from exterior observed-defect data. -/
theorem recover_hidden_memory
    (x y : J) :
    R.exteriorData (A.observedDefect x y) =
      B.memoryReadout (A.hiddenTotal x y) :=
  R.recover_hidden_memory_law x y

end GradeTwoMemoryRecoveryData

/-! ## 8. Thermodynamic Tomita/KMS bridge -/

/--
Horizon KMS memory bridge using the repository's thermodynamic/Tomita API.

This is the stronger socket tying the five-grade ledger to:

* a Tomita algebra/commutant split;
* a ring-level modular flow;
* a `HorizonKMSThermodynamics` KMS property;
* horizon temperature normalization.

The implication remains one-way and property-gated: hidden grade-two memory is
routed to the commutant and the reduced observer sees KMS thermality. This does
not assert information recovery.
-/
structure HorizonKMSThermodynamicMemoryBridge
    (J L Obs Memory Op : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [Ring Op]
    {G : FiveGrading L}
    (A : FiveGradeProjectedAccounting J L Obs G) where

  /-- Five-grade black-hole information ledger. -/
  ledger :
    BlackHoleInformationLedger J L Obs Memory A

  /-- Tomita algebra/commutant split for the horizon observer. -/
  tomita :
    TomitaCommutantDatum Op

  /-- Modular flow seen by the observer. -/
  modularFlow :
    InfoGeometry.OperatorAlgebra.Thermodynamics.ModularFlow Op

  /-- Inverse temperature. -/
  beta :
    ℝ

  /-- Horizon/KMS thermodynamic property. -/
  horizonKMS :
    InfoGeometry.OperatorAlgebra.Thermodynamics.HorizonKMSThermodynamics
      Op tomita modularFlow beta

  /-- Horizon temperature normalization. -/
  normalization :
    HorizonKMSNormalization

  /-- The thermodynamic inverse temperature matches the horizon normalization. -/
  beta_matches_horizon :
    beta = normalization.beta

  /--
  Map grade-two memory readouts into the observer's operator algebra.

  This represents the route by which hidden memory is stored as commutant-side
  data.
  -/
  memoryToOperator :
    Memory → Op

  /-- Hidden grade-two memory lands in the commutant sector. -/
  hidden_memory_in_commutant :
    ∀ x y : J,
      memoryToOperator (ledger.memoryReadout (A.hiddenTotal x y)) ∈ tomita.Mcomm



namespace HorizonKMSThermodynamicMemoryBridge

variable
    {J L Obs Memory Op : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [Ring Op]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}

variable (H : HorizonKMSThermodynamicMemoryBridge J L Obs Memory Op A)

/--
The observed three-grade defect is the projection of hidden grade-two memory.
-/
theorem observedDefect_eq_obs_hidden_sum
    (x y : J) :
    A.observedDefect x y =
      A.obs (A.hiddenTotal x y) :=
  A.observedDefect_eq_obs_hidden x y

/--
The observed three-grade defect is the visible projection of hidden grade-two
memory.
-/
theorem observed_defect_is_hidden_projection
    (x y : J) :
    A.observedDefect x y =
      visibleHiddenProjection H.ledger x y :=
  observedDefect_eq_visibleHiddenProjection H.ledger x y

/-- Grade-two memory lands in the commutant side of the Tomita split. -/
theorem hidden_memory_mem_commutant
    (x y : J) :
    H.memoryToOperator (H.ledger.memoryReadout (A.hiddenTotal x y)) ∈
      H.tomita.Mcomm :=
  H.hidden_memory_in_commutant x y

/-- The local observer sees a KMS state. -/
theorem observer_sees_kms :
    ∃ ω :
      InfoGeometry.OperatorAlgebra.Thermodynamics.KMSState
        Op H.modularFlow.toFlowDatum H.beta,
      ω.state.eval = H.horizonKMS.thermalization.reduction.observableEval :=
  H.horizonKMS.observer_sees_kms

/-- The reduced observer state carries a KMS boundary property. -/
def reduced_state_is_kms :
    InfoGeometry.OperatorAlgebra.Thermodynamics.KMSAnalyticBoundary
      H.horizonKMS.thermalization.reduction.observableEval
      H.modularFlow
      H.beta :=
  H.horizonKMS.reduced_state_is_kms

/-- The inverse temperature is calibrated as `2π / κ` in natural units. -/
theorem beta_eq_two_pi_over_surfaceGravity :
    H.beta =
      (2 * Real.pi) / H.normalization.surfaceGravity := by
  rw [H.beta_matches_horizon]
  exact H.normalization.beta_eq_two_pi_over_surfaceGravity

/-- The thermodynamic inverse temperature is positive. -/
theorem beta_pos :
    0 < H.beta := by
  rw [H.beta_matches_horizon]
  exact H.normalization.beta_pos

/-- The thermodynamic inverse temperature is nonzero. -/
theorem beta_ne_zero :
    H.beta ≠ 0 :=
  ne_of_gt H.beta_pos

/-- The horizon temperature is `κ / 2π` in natural units. -/
theorem temperature_eq_surfaceGravity_over_two_pi :
    H.normalization.temperature =
      H.normalization.surfaceGravity / (2 * Real.pi) :=
  H.normalization.temperature_eq_surfaceGravity_over_two_pi

/--
On observable algebra elements, the thermal readout agrees with the global
readout supplied by the observer reduction.
-/
theorem thermal_agrees_with_global_on_observable
    {X : Op}
    (hX : X ∈ H.tomita.M) :
    H.horizonKMS.thermalization.thermal.state.eval X =
      H.horizonKMS.thermalization.reduction.globalEval X :=
  H.horizonKMS.thermalization.thermal_agrees_with_global_on_observable hX



end HorizonKMSThermodynamicMemoryBridge

/-! ## 9. Owner target -/

/--
Owner target for installing a horizon KMS five-grade bridge.
-/
def HorizonKMSFiveGradeBridgeOwnerTarget
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory] : Prop :=
  ∀ G : FiveGrading L,
  ∀ A : FiveGradeProjectedAccounting J L Obs G,
  ∀ H : HorizonKMSFiveGradeBridge J L Obs Memory A,
  ∀ x y : J,
    H.heatCalibration.observedHeat (A.observedDefect x y) =
      H.heatCalibration.memoryHeat
        (H.ledger.memoryReadout (A.hiddenTotal x y))

/-!
The installed-owner name is retained as an API alias, but its proposition is
owned by `HorizonKMSFiveGradeBridgeOwnerTarget` above.
-/
abbrev HorizonKMSFiveGradeBridgeInstalledTarget
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory] : Prop :=
  HorizonKMSFiveGradeBridgeOwnerTarget J L Obs Memory

/--
The installed-owner target follows from the supplied bridge property.
-/
theorem horizonKMSFiveGradeBridgeInstalledTarget
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory] :
    HorizonKMSFiveGradeBridgeInstalledTarget J L Obs Memory := by
  intro G A H x y
  exact H.observed_heat_eq_gradeTwo_memory_heat x y

/--
Owner target for grade-two memory recovery.

This remains separate from KMS thermality.
-/
def GradeTwoMemoryRecoveryOwnerTarget
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory] : Prop :=
  ∀ G : FiveGrading L,
  ∀ A : FiveGradeProjectedAccounting J L Obs G,
  ∀ B : BlackHoleInformationLedger J L Obs Memory A,
    ∃ exteriorData : Obs → Memory,
      ∀ x y : J,
        exteriorData (A.observedDefect x y) =
          B.memoryReadout (A.hiddenTotal x y)

/--
Owner target for the thermodynamic/Tomita horizon KMS memory bridge.
-/
def HorizonKMSThermodynamicMemoryBridgeOwnerTarget
    (J L Obs Memory Op : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    [Ring Op] : Prop :=
  ∀ G : FiveGrading L,
  ∀ A : FiveGradeProjectedAccounting J L Obs G,
  ∀ H : HorizonKMSThermodynamicMemoryBridge (G := G) J L Obs Memory Op A,
    H.beta = H.normalization.beta ∧
      (∀ x y : J,
        H.memoryToOperator (H.ledger.memoryReadout (A.hiddenTotal x y)) ∈ H.tomita.Mcomm)

/-! ## 10. Exterior KMS flow calibration structure -/

/--
Exterior KMS flow calibration structure.

Proof-carrying reinstantiation of `exterior_kms_flow_calibration`.

Certifies that an exterior KMS flow (supplied by a `HorizonKMSFiveGradeBridge`)
equals a designated horizon modular flow — the Bisognano–Wichmann
identification for a Rindler/black-hole exterior.

This is a module-level structure that wraps a `HorizonKMSFiveGradeBridge`
and supplies the modular flow datum together with the explicit intertwining
equation:

  `∀ t X, kms.flow t X = modularFlowHorizon t X`.

See: Bisognano–Wichmann, J. Math. Phys. 17 (1976) 303.
-/
structure ExteriorKMSFlowCalibration
    (J L Obs Memory : Type*)
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    (H : HorizonKMSFiveGradeBridge J L Obs Memory A) where

  /-- The horizon modular flow on the exterior observable space. -/
  modularFlowHorizon : ℝ → Obs → Obs

  /-- Zero-time identity for the horizon modular flow. -/
  modularFlowHorizon_zero :
    ∀ X : Obs, modularFlowHorizon 0 X = X

  /-- Additive law for the horizon modular flow. -/
  modularFlowHorizon_add :
    ∀ (s t : ℝ) (X : Obs),
      modularFlowHorizon (s + t) X =
        modularFlowHorizon s (modularFlowHorizon t X)

  /--
  Bisognano–Wichmann calibration:
  the KMS flow equals the horizon modular flow.

  `∀ t X, kms.flow t X = modularFlowHorizon t X`.
  -/
  exterior_kms_flow_eq_modular :
    ∀ (t : ℝ) (X : Obs),
      H.kms.flow t X = modularFlowHorizon t X

namespace ExteriorKMSFlowCalibration

variable
    {J L Obs Memory : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup Obs] [Module ℝ Obs]
    [AddCommGroup Memory] [Module ℝ Memory]
    {G : FiveGrading L}
    {A : FiveGradeProjectedAccounting J L Obs G}
    {H : HorizonKMSFiveGradeBridge J L Obs Memory A}

variable (E : ExteriorKMSFlowCalibration J L Obs Memory H)

/-- The KMS flow equals the horizon modular flow. -/
theorem kms_flow_eq_horizon_modular (t : ℝ) (X : Obs) :
    H.kms.flow t X = E.modularFlowHorizon t X :=
  E.exterior_kms_flow_eq_modular t X

/-- KMS state is invariant under the horizon modular flow. -/
theorem kms_state_invariant_horizon_flow (t : ℝ) (X : Obs) :
    H.kms.state (E.modularFlowHorizon t X) = H.kms.state X := by
  rw [← E.kms_flow_eq_horizon_modular]
  exact H.kms.flow_invariant t X

end ExteriorKMSFlowCalibration

end InfoGeometry.OperatorAlgebra.HorizonKMS

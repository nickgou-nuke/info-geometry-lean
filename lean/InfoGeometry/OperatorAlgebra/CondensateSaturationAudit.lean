/-
InfoGeometry/OperatorAlgebra/CondensateSaturationAudit.lean

Capacity and saturation audit for a hidden condensate/commutant ledger.

This module does not prove cosmological saturation or horizon failure.
It defines the witness structure needed to say that a condensate is near
capacity and that an Andreev/modular mirror is beginning to fail.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CondensateSaturationAudit

/-! ## 1. Capacity witness -/

/--
Capacity witness for a hidden condensate / commutant memory sector.

`capacity` is the installed entropy/information bound.
`load` is the current hidden-memory load.
`safetyMargin` is the tolerance below which the system is considered near
saturation.
-/
structure CondensateCapacityWitness
    (State : Type*) where
  capacity : ℝ
  load : State → ℝ
  safetyMargin : ℝ

  capacity_nonneg :
    0 ≤ capacity

  load_nonneg :
    ∀ s : State, 0 ≤ load s

  safetyMargin_nonneg :
    0 ≤ safetyMargin

namespace CondensateCapacityWitness

variable {State : Type*}
variable (C : CondensateCapacityWitness State)

/-- Remaining hidden-memory capacity. -/
def remainingCapacity
    (s : State) : ℝ :=
  C.capacity - C.load s

/-- Saturated means the installed load has reached or exceeded capacity. -/
def Saturated
    (s : State) : Prop :=
  C.remainingCapacity s ≤ 0

/-- Near saturation means the remaining capacity is within the safety margin. -/
def NearSaturation
    (s : State) : Prop :=
  C.remainingCapacity s ≤ C.safetyMargin

/-- Saturation implies near saturation. -/
theorem nearSaturation_of_saturated
    {s : State}
    (hsat : C.Saturated s) :
    C.NearSaturation s := by
  unfold Saturated NearSaturation at *
  linarith [C.safetyMargin_nonneg]

/-- If load exceeds capacity, the condensate is saturated. -/
theorem saturated_of_capacity_le_load
    {s : State}
    (h : C.capacity ≤ C.load s) :
    C.Saturated s := by
  unfold Saturated remainingCapacity
  linarith

end CondensateCapacityWitness

/-! ## 2. Mirror health witness -/

/--
Health audit for an Andreev/modular mirror.

This does not assert that the mirror is physically superconducting. It merely
records the operational readouts needed to detect leakage or accounting
failure.
-/
structure MirrorHealthWitness
    (State : Type*) where
  reflectionEfficiency : State → ℝ
  leakage : State → ℝ
  balanceResidual : State → ℝ

  minReflectionEfficiency : ℝ
  maxLeakage : ℝ
  maxBalanceResidual : ℝ

namespace MirrorHealthWitness

variable {State : Type*}
variable (M : MirrorHealthWitness State)

/-- The mirror is healthy if all operational readouts are within tolerance. -/
def Healthy
    (s : State) : Prop :=
  M.minReflectionEfficiency ≤ M.reflectionEfficiency s ∧
    M.leakage s ≤ M.maxLeakage ∧
      |M.balanceResidual s| ≤ M.maxBalanceResidual

/-- The mirror is failing if it is not healthy. -/
def Failing
    (s : State) : Prop :=
  ¬ M.Healthy s

/-- Excess leakage witnesses mirror failure. -/
theorem failing_of_leakage_gt
    {s : State}
    (h : M.maxLeakage < M.leakage s) :
    M.Failing s := by
  intro hhealthy
  exact not_lt_of_ge hhealthy.2.1 h

/-- Too-low reflection efficiency witnesses mirror failure. -/
theorem failing_of_reflection_lt
    {s : State}
    (h : M.reflectionEfficiency s < M.minReflectionEfficiency) :
    M.Failing s := by
  intro hhealthy
  exact not_lt_of_ge hhealthy.1 h

/-- Excess accounting residual witnesses mirror failure. -/
theorem failing_of_balanceResidual_gt
    {s : State}
    (h : M.maxBalanceResidual < |M.balanceResidual s|) :
    M.Failing s := by
  intro hhealthy
  exact not_lt_of_ge hhealthy.2.2 h

end MirrorHealthWitness

/-! ## 3. Modular flattening witness -/

/--
Modular flattening readout.

`deltaResidualToIdentity` is a model-supplied scalar measuring how close the
modular operator/readout is to the identity/tracial fixed point.

This is deliberately abstract; no norm on operators is assumed here.
-/
structure ModularFlatteningWitness
    (State : Type*) where
  deltaResidualToIdentity : State → ℝ
  flatteningThreshold : ℝ

namespace ModularFlatteningWitness

variable {State : Type*}
variable (F : ModularFlatteningWitness State)

/--
The modular sector is near tracial/flat if the residual to identity is below
the installed threshold.
-/
def NearTracial
    (s : State) : Prop :=
  F.deltaResidualToIdentity s ≤ F.flatteningThreshold

end ModularFlatteningWitness

/-! ## 4. Recovery backlog witness -/

/--
Recovery backlog readout.

This records how many hidden defects remain unrecovered by the current
revelation/recovery layer.
-/
structure RecoveryBacklogWitness
    (State : Type*) where
  unrecoveredDefectCount : State → ℕ
  maxUnrecoveredDefects : ℕ

namespace RecoveryBacklogWitness

variable {State : Type*}
variable (R : RecoveryBacklogWitness State)

/-- The recovery backlog is excessive. -/
def Excessive
    (s : State) : Prop :=
  R.maxUnrecoveredDefects < R.unrecoveredDefectCount s

end RecoveryBacklogWitness

/-! ## 5. Composite saturation audit -/

/--
Composite audit for condensate saturation.

This is the specific witness that determines whether the current aeon's
condensate is nearing saturation.
-/
structure CondensateSaturationWitness
    (State : Type*) where
  capacity :
    CondensateCapacityWitness State

  mirror :
    MirrorHealthWitness State

  modular :
    ModularFlatteningWitness State

  backlog :
    RecoveryBacklogWitness State

namespace CondensateSaturationWitness

variable {State : Type*}
variable (A : CondensateSaturationWitness State)

/--
The condensate is under saturation warning if any installed warning channel is
active.
-/
def SaturationWarning
    (s : State) : Prop :=
  A.capacity.NearSaturation s ∨
    A.mirror.Failing s ∨
      A.modular.NearTracial s ∨
        A.backlog.Excessive s

/-- Saturation implies a saturation warning. -/
theorem warning_of_saturated
    {s : State}
    (hsat : A.capacity.Saturated s) :
    A.SaturationWarning s := by
  exact Or.inl (A.capacity.nearSaturation_of_saturated hsat)

/-- Mirror leakage implies a saturation warning. -/
theorem warning_of_leakage_gt
    {s : State}
    (h : A.mirror.maxLeakage < A.mirror.leakage s) :
    A.SaturationWarning s := by
  exact Or.inr <| Or.inl (A.mirror.failing_of_leakage_gt h)

/-- Reflection-efficiency loss implies a saturation warning. -/
theorem warning_of_reflection_lt
    {s : State}
    (h : A.mirror.reflectionEfficiency s < A.mirror.minReflectionEfficiency) :
    A.SaturationWarning s := by
  exact Or.inr <| Or.inl (A.mirror.failing_of_reflection_lt h)

/-- Mirror accounting residual implies a saturation warning. -/
theorem warning_of_balanceResidual_gt
    {s : State}
    (h : A.mirror.maxBalanceResidual < |A.mirror.balanceResidual s|) :
    A.SaturationWarning s := by
  exact Or.inr <| Or.inl (A.mirror.failing_of_balanceResidual_gt h)

/-- Modular flattening implies a saturation warning. -/
theorem warning_of_nearTracial
    {s : State}
    (h : A.modular.NearTracial s) :
    A.SaturationWarning s := by
  exact Or.inr <| Or.inr <| Or.inl h

/-- Excess recovery backlog implies a saturation warning. -/
theorem warning_of_excessive_backlog
    {s : State}
    (h : A.backlog.Excessive s) :
    A.SaturationWarning s := by
  exact Or.inr <| Or.inr <| Or.inr h

end CondensateSaturationWitness

end InfoGeometry.OperatorAlgebra.CondensateSaturationAudit

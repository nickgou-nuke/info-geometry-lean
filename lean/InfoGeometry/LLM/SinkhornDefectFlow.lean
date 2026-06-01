import InfoGeometry.LLM.TrialityMoE
import InfoGeometry.Canonical.WindingOrbitClosure
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.RelativePotentialCountBridge

/-!
# Sinkhorn Defect Flow Owner Surface

Owner-level defect flow surface for Sinkhorn-side router updates.
Primary defect is the relative-volume (Radon-Nikodym barrier) trajectory; the
odd-sector norm channel is kept as a derived router readout.
This module intentionally avoids interpretation language and exposes only
operator inequalities on the defect budget.
-/

namespace InfoGeometry.LLM.SinkhornDefectFlow

open InfoGeometry.LLM.TrialityMoE
open InfoGeometry.LLM.TrialityMoE.RouterDefectBoundBridge
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.ModularSourceBridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Odd-sector defect functional attached to a bounded router residual. -/
noncomputable def δ_odd (B : RouterDefectBoundBridge (E := E)) : ℝ :=
  ‖B.routerResidual‖

/-- Equilibrium condition: odd-sector defect functional vanishes. -/
def IsRouterEquilibrium (B : RouterDefectBoundBridge (E := E)) : Prop :=
  δ_odd B = 0

theorem δ_odd_nonneg (B : RouterDefectBoundBridge (E := E)) :
    0 ≤ δ_odd B := by
  unfold δ_odd
  exact norm_nonneg B.routerResidual

theorem δ_odd_le_ZD (B : RouterDefectBoundBridge (E := E)) :
    δ_odd B ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD B.CIK‖ := by
  simpa [δ_odd] using B.residual_norm_le_ZD

/--
Thermodynamic odd-sector readout for the corrected D3 bridge.

This is not an ambient operator norm. It is the explicit readout supplied by
the Weyl/thermodynamic comparison packet attached to the router bridge.
-/
noncomputable def δ_odd_thermo
    (B : RouterDefectThermodynamicBridge (E := E)) : ℝ :=
  B.comparison.operatorInformationNormReadout B.routerResidual

/-- Central `Z_D` thermodynamic readout on the same comparison packet. -/
noncomputable def δ_ZD_thermo
    (B : RouterDefectThermodynamicBridge (E := E)) : ℝ :=
  B.comparison.operatorInformationNormReadout
    (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) B.CIK)

/--
Corrected D3 readout bound: the thermodynamic router defect is bounded by the
thermodynamic `Z_D` readout through the shared Weyl/relative-potential lane.
-/
theorem δ_odd_thermo_le_ZD
    (B : RouterDefectThermodynamicBridge (E := E)) :
    δ_odd_thermo B ≤ δ_ZD_thermo B := by
  simpa [δ_odd_thermo, δ_ZD_thermo] using
    RouterDefectThermodynamicBridge.operatorInformationNormReadout_routerResidual_le_ZD
      (E := E) B

/-- `δ_odd = 0` is exactly residual equilibrium. -/
theorem δ_odd_eq_zero_iff_equilibrium (B : RouterDefectBoundBridge (E := E)) :
    δ_odd B = 0 ↔ IsRouterEquilibrium B := by
  rfl

/-- Vanishing odd-sector defect is exactly vanishing router residual by operator-norm separation. -/
theorem δ_odd_eq_zero_iff_routerResidual_eq_zero (B : RouterDefectBoundBridge (E := E)) :
    δ_odd B = 0 ↔ B.routerResidual = 0 := by
  unfold δ_odd
  exact ContinuousLinearMap.opNorm_zero_iff B.routerResidual

theorem equilibrium_of_δ_odd_eq_zero
    (B : RouterDefectBoundBridge (E := E))
    (hδ : δ_odd B = 0) :
    IsRouterEquilibrium B := hδ

/--
If the exact deviation channel is controlled by `Z_D` and `Z_D` itself
vanishes, then the bounded router residual produced from the canonical observer
lane has zero odd-sector defect.
-/
@[simp] theorem ofZDControlledObserver_δ_odd_eq_zero_of_ZD_eq_zero
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (obs : InfoGeometry.Canonical.ObserverDefect.ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : InfoGeometry.Canonical.ObserverDefect.ObserverDeviationControlledByZD CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    δ_odd (ofZDControlledObserver (E := E) CIK obs flow hControl) = 0 := by
  unfold δ_odd
  rw [ofZDControlledObserver_routerResidual_eq_zero_of_ZD_eq_zero
    (E := E) (CIK := CIK) (obs := obs) (flow := flow) (hControl := hControl) (hZD := hZD)]
  exact ContinuousLinearMap.opNorm_zero

/--
If the exact deviation channel is controlled by `Z_D` and `Z_D` itself
vanishes, then the canonical observer route is already in Sinkhorn
router-equilibrium.
-/
theorem ofZDControlledObserver_isRouterEquilibrium_of_ZD_eq_zero
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (obs : InfoGeometry.Canonical.ObserverDefect.ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : InfoGeometry.Canonical.ObserverDefect.ObserverDeviationControlledByZD CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    IsRouterEquilibrium (ofZDControlledObserver (E := E) CIK obs flow hControl) := by
  exact equilibrium_of_δ_odd_eq_zero (E := E)
    (ofZDControlledObserver (E := E) CIK obs flow hControl)
    (ofZDControlledObserver_δ_odd_eq_zero_of_ZD_eq_zero
      (E := E) (CIK := CIK) (obs := obs) (flow := flow) (hControl := hControl) (hZD := hZD))

/--
An aligned observer has zero odd-sector defect on the Sinkhorn router lane.
-/
@[simp] theorem ofAlignedObserver_δ_odd_eq_zero
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (obs : InfoGeometry.Canonical.ObserverDefect.ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : InfoGeometry.Canonical.ObserverDefect.observerOrientationResidual CIK obs = 0) :
    δ_odd (ofAlignedObserver (E := E) CIK obs flow hAlign) = 0 := by
  unfold δ_odd
  rw [ofAlignedObserver_routerResidual
    (E := E) (CIK := CIK) (obs := obs) (flow := flow) (hAlign := hAlign)]
  exact ContinuousLinearMap.opNorm_zero

/--
An aligned observer is already in Sinkhorn router-equilibrium.
-/
theorem ofAlignedObserver_isRouterEquilibrium
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (obs : InfoGeometry.Canonical.ObserverDefect.ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : InfoGeometry.Canonical.ObserverDefect.observerOrientationResidual CIK obs = 0) :
    IsRouterEquilibrium (ofAlignedObserver (E := E) CIK obs flow hAlign) := by
  exact equilibrium_of_δ_odd_eq_zero (E := E)
    (ofAlignedObserver (E := E) CIK obs flow hAlign)
    (ofAlignedObserver_δ_odd_eq_zero
      (E := E) (CIK := CIK) (obs := obs) (flow := flow) (hAlign := hAlign))

/--
A strain-zero observer has zero odd-sector defect on the Sinkhorn router lane.
-/
@[simp] theorem ofStrainZeroObserver_δ_odd_eq_zero
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (obs : InfoGeometry.Canonical.ObserverDefect.ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hStrain : InfoGeometry.Canonical.ObserverDefect.observerOrientationStrain CIK obs = 0) :
    δ_odd (ofStrainZeroObserver (E := E) CIK obs flow hStrain) = 0 := by
  unfold δ_odd
  rw [ofStrainZeroObserver_routerResidual
    (E := E) (CIK := CIK) (obs := obs) (flow := flow) (hStrain := hStrain)]
  exact ContinuousLinearMap.opNorm_zero

/--
A strain-zero observer is already in Sinkhorn router-equilibrium.
-/
theorem ofStrainZeroObserver_isRouterEquilibrium
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (obs : InfoGeometry.Canonical.ObserverDefect.ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hStrain : InfoGeometry.Canonical.ObserverDefect.observerOrientationStrain CIK obs = 0) :
    IsRouterEquilibrium (ofStrainZeroObserver (E := E) CIK obs flow hStrain) := by
  exact equilibrium_of_δ_odd_eq_zero (E := E)
    (ofStrainZeroObserver (E := E) CIK obs flow hStrain)
    (ofStrainZeroObserver_δ_odd_eq_zero
      (E := E) (CIK := CIK) (obs := obs) (flow := flow) (hStrain := hStrain))

/-- The sourced-generator deviation is exactly `δ_odd`. -/
theorem sourcedGenerator_deviation_eq_δ_odd
    (B : RouterDefectBoundBridge (E := E)) :
    ‖B.sourcedGenerator - B.flow.K0‖ = δ_odd B := by
  unfold InfoGeometry.LLM.TrialityMoE.RouterDefectBoundBridge.sourcedGenerator δ_odd
  simp [sub_eq_add_neg, add_assoc]

/--
One-step Sinkhorn update wrapper carrying monotone defect reduction as an owner
obligation.
-/
structure SinkhornDefectStep (B : RouterDefectBoundBridge (E := E)) where
  next : RouterDefectBoundBridge (E := E)
  δ_odd_next_le_δ_odd : δ_odd next ≤ δ_odd B

theorem δ_odd_next_le_δ_odd
    {B : RouterDefectBoundBridge (E := E)}
    (step : SinkhornDefectStep B) :
    δ_odd step.next ≤ δ_odd B :=
  step.δ_odd_next_le_δ_odd

theorem sourcedGenerator_deviation_next_le
    {B : RouterDefectBoundBridge (E := E)}
    (step : SinkhornDefectStep B) :
    ‖step.next.sourcedGenerator - step.next.flow.K0‖ ≤ ‖B.sourcedGenerator - B.flow.K0‖ := by
  rw [sourcedGenerator_deviation_eq_δ_odd step.next,
    sourcedGenerator_deviation_eq_δ_odd B]
  exact step.δ_odd_next_le_δ_odd

/--
Construct a one-step defect reduction from an actual zero-residual proof.

This is not an assumed monotonicity field: the inequality is derived from
`ContinuousLinearMap.opNorm_zero` and nonnegativity of the current odd defect.
-/
def SinkhornDefectStep.of_routerResidual_eq_zero
    (B next : RouterDefectBoundBridge (E := E))
    (hNext : next.routerResidual = 0) :
    SinkhornDefectStep (E := E) B :=
  { next := next
    δ_odd_next_le_δ_odd := by
      unfold δ_odd
      rw [hNext]
      calc
        ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
        _ ≤ ‖B.routerResidual‖ := norm_nonneg B.routerResidual }

@[simp] theorem SinkhornDefectStep.of_routerResidual_eq_zero_next
    (B next : RouterDefectBoundBridge (E := E))
    (hNext : next.routerResidual = 0) :
    (SinkhornDefectStep.of_routerResidual_eq_zero (E := E) B next hNext).next = next :=
  rfl

/--
Zero residual in the next state gives monotone sourced-generator deviation.
-/
theorem sourcedGenerator_deviation_next_le_of_routerResidual_eq_zero
    (B next : RouterDefectBoundBridge (E := E))
    (hNext : next.routerResidual = 0) :
    ‖next.sourcedGenerator - next.flow.K0‖ ≤ ‖B.sourcedGenerator - B.flow.K0‖ := by
  simpa using
    sourcedGenerator_deviation_next_le
      (E := E)
      (SinkhornDefectStep.of_routerResidual_eq_zero (E := E) B next hNext)

/--
One-step Sinkhorn update wrapper on the corrected thermodynamic readout lane.
-/
structure SinkhornThermodynamicDefectStep
    (B : RouterDefectThermodynamicBridge (E := E)) where
  next : RouterDefectThermodynamicBridge (E := E)
  δ_odd_thermo_next_le :
    δ_odd_thermo next ≤ δ_odd_thermo B

theorem δ_odd_thermo_next_le
    {B : RouterDefectThermodynamicBridge (E := E)}
    (step : SinkhornThermodynamicDefectStep (E := E) B) :
    δ_odd_thermo step.next ≤ δ_odd_thermo B :=
  step.δ_odd_thermo_next_le

/--
Owner bridge from LLM residual budget to the non-equilibrium clock-defect lane.
-/
structure RouterClockDefectBridge where
  bound : RouterDefectBoundBridge (E := E)
  hMod : EndH
  residual_eq_clockDefect :
    bound.routerResidual =
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod

namespace RouterClockDefectBridge

/--
Canonical clock-defect constructor.

The router residual is fixed to the canonical non-equilibrium clock defect. The
remaining `ZD` bound is explicit: it must be proved upstream rather than hidden
inside an arbitrary residual field.
-/
noncomputable def ofCanonicalClockDefect
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (hBound :
      ‖InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod‖ ≤
        ‖InfoGeometry.Canonical.KKTClosure.ZD CIK‖) :
    RouterClockDefectBridge (E := E) :=
  { bound :=
      { CIK := CIK
        flow := flow
        routerResidual :=
          InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod
        residual_norm_le_ZD := hBound }
    hMod := hMod
    residual_eq_clockDefect := rfl }

@[simp] theorem ofCanonicalClockDefect_routerResidual
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (hBound :
      ‖InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod‖ ≤
        ‖InfoGeometry.Canonical.KKTClosure.ZD CIK‖) :
    (ofCanonicalClockDefect (E := E) CIK flow hMod hBound).bound.routerResidual =
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod := by
  rfl

/--
Detailed equilibrium closes the non-equilibrium clock-defect `Z_D` budget:
the clock defect itself is zero, so only `0 ≤ ‖Z_D‖` remains.
-/
@[rep_depth transport]
theorem nonEquilibriumClockDefect_norm_le_ZD_of_detailedEquilibrium
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (hMod : EndH)
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) hMod) :
    ‖InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod‖ ≤
      ‖InfoGeometry.Canonical.KKTClosure.ZD CIK‖ := by
  have hZero :
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod = 0 :=
    InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect_eq_zero_of_detailedEquilibrium
      (H := E) hMod hEq
  rw [hZero]
  calc
    ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
    _ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD CIK‖ :=
      norm_nonneg (InfoGeometry.Canonical.KKTClosure.ZD CIK)

/--
Zero-defect clock bridge for detailed equilibrium.

Detailed equilibrium kills the canonical non-equilibrium clock defect, so the
`ZD` budget is closed without an independent bound assumption.
-/
noncomputable def ofDetailedEquilibrium
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) hMod) :
    RouterClockDefectBridge (E := E) :=
  ofCanonicalClockDefect (E := E) CIK flow hMod
    (nonEquilibriumClockDefect_norm_le_ZD_of_detailedEquilibrium (E := E) (CIK := CIK) (hMod := hMod) hEq)

@[simp] theorem ofDetailedEquilibrium_routerResidual
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) hMod) :
    (ofDetailedEquilibrium (E := E) CIK flow hMod hEq).bound.routerResidual = 0 := by
  have hZero :
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) hMod = 0 :=
    InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect_eq_zero_of_detailedEquilibrium
      (H := E) hMod hEq
  simpa [ofDetailedEquilibrium] using hZero

@[simp] theorem ofDetailedEquilibrium_δ_odd_eq_zero
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) hMod) :
    δ_odd (ofDetailedEquilibrium (E := E) CIK flow hMod hEq).bound = 0 := by
  unfold δ_odd
  rw [ofDetailedEquilibrium_routerResidual (E := E) (CIK := CIK) (flow := flow)
    (hMod := hMod) (hEq := hEq)]
  exact ContinuousLinearMap.opNorm_zero

theorem ofDetailedEquilibrium_isRouterEquilibrium
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) hMod) :
    IsRouterEquilibrium (ofDetailedEquilibrium (E := E) CIK flow hMod hEq).bound := by
  exact equilibrium_of_δ_odd_eq_zero (E := E)
    (ofDetailedEquilibrium (E := E) CIK flow hMod hEq).bound
    (ofDetailedEquilibrium_δ_odd_eq_zero (E := E) (CIK := CIK) (flow := flow)
      (hMod := hMod) (hEq := hEq))

/--
Witness-routed detailed-equilibrium constructor on the clock-defect bridge.

This removes the bare `hEq` proof argument for callers that already own the
explicit `DetailedEquilibriumWitness` packet on the winding owner lane.
-/
noncomputable def ofDetailedEquilibriumWitness
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (W : InfoGeometry.Canonical.WindingOrbitClosure.DetailedEquilibriumWitness (H := E) hMod) :
    RouterClockDefectBridge (E := E) :=
  ofDetailedEquilibrium (E := E) CIK flow hMod W.hEq

@[simp] theorem ofDetailedEquilibriumWitness_routerResidual
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (W : InfoGeometry.Canonical.WindingOrbitClosure.DetailedEquilibriumWitness (H := E) hMod) :
    (ofDetailedEquilibriumWitness (E := E) CIK flow hMod W).bound.routerResidual = 0 := by
  simpa [ofDetailedEquilibriumWitness] using
    ofDetailedEquilibrium_routerResidual (E := E) (CIK := CIK) (flow := flow)
      (hMod := hMod) (hEq := W.hEq)

@[simp] theorem ofDetailedEquilibriumWitness_δ_odd_eq_zero
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (W : InfoGeometry.Canonical.WindingOrbitClosure.DetailedEquilibriumWitness (H := E) hMod) :
    δ_odd (ofDetailedEquilibriumWitness (E := E) CIK flow hMod W).bound = 0 := by
  simpa [ofDetailedEquilibriumWitness] using
    ofDetailedEquilibrium_δ_odd_eq_zero (E := E) (CIK := CIK) (flow := flow)
      (hMod := hMod) (hEq := W.hEq)

theorem ofDetailedEquilibriumWitness_isRouterEquilibrium
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel H₂)
    (flow : BackgroundModularFlow CIK)
    (hMod : EndH)
    (W : InfoGeometry.Canonical.WindingOrbitClosure.DetailedEquilibriumWitness (H := E) hMod) :
    IsRouterEquilibrium (ofDetailedEquilibriumWitness (E := E) CIK flow hMod W).bound := by
  simpa [ofDetailedEquilibriumWitness] using
    ofDetailedEquilibrium_isRouterEquilibrium (E := E) (CIK := CIK) (flow := flow)
      (hMod := hMod) (hEq := W.hEq)

end RouterClockDefectBridge

/--
On the clock-defect bridge, odd-sector defect is exactly the non-equilibrium
clock-defect norm.
-/
theorem δ_odd_eq_clockDefect_norm
    (B : RouterClockDefectBridge (E := E)) :
    δ_odd B.bound =
      ‖InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) B.hMod‖ := by
  simp [δ_odd, B.residual_eq_clockDefect]

/-- Router equilibrium on a clock-defect bridge is exactly zero canonical clock defect. -/
theorem router_equilibrium_iff_clockDefect_eq_zero
    (B : RouterClockDefectBridge (E := E)) :
    IsRouterEquilibrium B.bound ↔
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) B.hMod = 0 := by
  exact
    (δ_odd_eq_zero_iff_routerResidual_eq_zero (E := E) B.bound).trans
      (by
        constructor
        · intro hResidual
          simpa [B.residual_eq_clockDefect] using hResidual
        · intro hClock
          simpa [B.residual_eq_clockDefect] using hClock)

/-- Router equilibrium is equivalent to the owner detailed-equilibrium condition. -/
theorem router_equilibrium_iff_detailedEquilibrium
    (B : RouterClockDefectBridge (E := E)) :
    IsRouterEquilibrium B.bound ↔
      InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) B.hMod := by
  exact
    (router_equilibrium_iff_clockDefect_eq_zero (E := E) B).trans
      (InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect_eq_zero_iff_detailedEquilibrium
        (H := E) B.hMod)

/--
Detailed equilibrium (`scalePart = 0`) forces vanishing odd-sector defect on
the clock-defect bridge.
-/
theorem δ_odd_eq_zero_of_detailedEquilibrium
    (B : RouterClockDefectBridge (E := E))
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) B.hMod) :
    δ_odd B.bound = 0 := by
  rw [δ_odd_eq_clockDefect_norm (E := E) B]
  have hZero :
      InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect (H := E) B.hMod = 0 :=
    InfoGeometry.Canonical.WindingOrbitClosure.nonEquilibriumClockDefect_eq_zero_of_detailedEquilibrium
      (H := E) B.hMod hEq
  rw [hZero]
  exact ContinuousLinearMap.opNorm_zero

/--
Detailed equilibrium implies router-equilibrium on the clock-defect bridge.
-/
theorem router_equilibrium_of_detailedEquilibrium
    (B : RouterClockDefectBridge (E := E))
    (hEq : InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) B.hMod) :
    IsRouterEquilibrium B.bound := by
  exact equilibrium_of_δ_odd_eq_zero (E := E) B.bound
    (δ_odd_eq_zero_of_detailedEquilibrium (E := E) B hEq)

/--
Witness-routed zero-defect theorem on the clock-defect bridge.

This removes the bare detailed-equilibrium proposition in favor of the explicit
`DetailedEquilibriumWitness` packet.
-/
theorem δ_odd_eq_zero_of_detailedEquilibriumWitness
    (B : RouterClockDefectBridge (E := E))
    (W : InfoGeometry.Canonical.WindingOrbitClosure.DetailedEquilibriumWitness (H := E) B.hMod) :
    δ_odd B.bound = 0 :=
  δ_odd_eq_zero_of_detailedEquilibrium (E := E) B W.hEq

/--
Witness-routed router-equilibrium theorem on the clock-defect bridge.

This removes the bare detailed-equilibrium proposition in favor of the explicit
`DetailedEquilibriumWitness` packet.
-/
theorem router_equilibrium_of_detailedEquilibriumWitness
    (B : RouterClockDefectBridge (E := E))
    (W : InfoGeometry.Canonical.WindingOrbitClosure.DetailedEquilibriumWitness (H := E) B.hMod) :
    IsRouterEquilibrium B.bound :=
  router_equilibrium_of_detailedEquilibrium (E := E) B W.hEq

/--
Positive odd-sector defect implies noncommuting scale lane on the same
clock-defect bridge.
-/
theorem noncommutingScaleLane_of_δ_odd_pos
    (B : RouterClockDefectBridge (E := E))
    (hδ : 0 < δ_odd B.bound) :
    InfoGeometry.Canonical.WindingOrbitClosure.IsNoncommutingScaleLane (H := E) B.hMod := by
  unfold InfoGeometry.Canonical.WindingOrbitClosure.IsNoncommutingScaleLane
  intro hZero
  have hδZero : δ_odd B.bound = 0 := by
    rw [δ_odd_eq_clockDefect_norm (E := E) B]
    rw [hZero]
    exact ContinuousLinearMap.opNorm_zero
  exact (ne_of_gt hδ) hδZero

/--
Positive odd-sector defect excludes detailed equilibrium on the same
clock-defect bridge.
-/
theorem not_detailedEquilibrium_of_δ_odd_pos
    (B : RouterClockDefectBridge (E := E))
    (hδ : 0 < δ_odd B.bound) :
    ¬ InfoGeometry.Canonical.WindingOrbitClosure.IsDetailedEquilibriumSeed (H := E) B.hMod := by
  exact InfoGeometry.Canonical.WindingOrbitClosure.not_detailedEquilibrium_of_noncommutingScaleLane
    (H := E) B.hMod
    (noncommutingScaleLane_of_δ_odd_pos (E := E) B hδ)

/--
Executable Sinkhorn defect-reduction update operator.
-/
structure SinkhornDefectUpdate where
  map : RouterDefectBoundBridge (E := E) → RouterDefectBoundBridge (E := E)
  δ_odd_map_le : ∀ B : RouterDefectBoundBridge (E := E), δ_odd (map B) ≤ δ_odd B

/--
`n`-step iteration of a Sinkhorn defect-reduction update.
-/
def iterate
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    RouterDefectBoundBridge (E := E) :=
  Nat.rec B0 (fun _ B => U.map B) n

@[simp] theorem iterate_zero
    (U : SinkhornDefectUpdate (E := E))
    (B0 : RouterDefectBoundBridge (E := E)) :
    iterate (E := E) U 0 B0 = B0 := rfl

@[simp] theorem iterate_succ
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    iterate (E := E) U (n + 1) B0 = U.map (iterate (E := E) U n B0) := by
  rfl

/--
One-step monotone defect reduction along the executable iterator.
-/
theorem δ_odd_iterate_succ_le_iterate
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    δ_odd (iterate (E := E) U (n + 1) B0) ≤ δ_odd (iterate (E := E) U n B0) := by
  simpa [iterate_succ] using U.δ_odd_map_le (iterate (E := E) U n B0)

/--
Defect budget is globally bounded by the initial state along the executable
Sinkhorn iterator.
-/
theorem δ_odd_iterate_le_initial
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    δ_odd (iterate (E := E) U n B0) ≤ δ_odd B0 := by
  induction n with
  | zero =>
      simp [iterate_zero]
  | succ n ih =>
      exact le_trans (δ_odd_iterate_succ_le_iterate (E := E) U n B0) ih

/--
One-step sourced-generator deviation monotonicity along the executable iterator.
-/
theorem sourcedGenerator_deviation_iterate_succ_le_iterate
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    ‖(iterate (E := E) U (n + 1) B0).sourcedGenerator - (iterate (E := E) U (n + 1) B0).flow.K0‖
      ≤
    ‖(iterate (E := E) U n B0).sourcedGenerator - (iterate (E := E) U n B0).flow.K0‖ := by
  rw [sourcedGenerator_deviation_eq_δ_odd (E := E) (iterate (E := E) U (n + 1) B0),
    sourcedGenerator_deviation_eq_δ_odd (E := E) (iterate (E := E) U n B0)]
  exact δ_odd_iterate_succ_le_iterate (E := E) U n B0

/--
Global sourced-generator deviation bound by the initial state.
-/
theorem sourcedGenerator_deviation_iterate_le_initial
    (U : SinkhornDefectUpdate (E := E))
    (n : Nat)
    (B0 : RouterDefectBoundBridge (E := E)) :
    ‖(iterate (E := E) U n B0).sourcedGenerator - (iterate (E := E) U n B0).flow.K0‖
      ≤
    ‖B0.sourcedGenerator - B0.flow.K0‖ := by
  rw [sourcedGenerator_deviation_eq_δ_odd (E := E) (iterate (E := E) U n B0),
    sourcedGenerator_deviation_eq_δ_odd (E := E) B0]
  exact δ_odd_iterate_le_initial (E := E) U n B0

section VolumeAnomaly

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RelativePotentialCountBridge

/--
Primary relative-volume defect functional on a Sinkhorn trajectory:
the phase-aligned Radon-Nikodym barrier before step `k`.
-/
noncomputable def δ_relVol
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) : ℝ :=
  trajectoryRNBarrier n T k

/--
Backward-compatible name for `δ_relVol`.
-/
noncomputable def δ_volume
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) : ℝ :=
  δ_relVol n T k

@[simp] theorem δ_volume_eq_δ_relVol
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    δ_volume n T k = δ_relVol n T k := rfl

theorem δ_relVol_nonneg
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    0 ≤ δ_relVol n T k := by
  unfold δ_relVol trajectoryRNBarrier
  exact phaseRNBarrierBefore_nonneg (n := n) (phaseAt k) (T.state k)

theorem δ_volume_nonneg
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    0 ≤ δ_volume n T k := by
  simpa [δ_volume_eq_δ_relVol] using δ_relVol_nonneg (n := n) T k

theorem δ_relVol_next_le
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ δ_relVol n T k := by
  simpa [δ_relVol] using trajectoryRNBarrier_monotone (n := n) T k

theorem δ_volume_next_le
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ δ_volume n T k := by
  simpa [δ_volume_eq_δ_relVol] using δ_relVol_next_le (n := n) T k

/--
One-step available RN work/heat budget.

This is scalar thermodynamic bookkeeping on the Sinkhorn RN barrier: the amount
of relative-volume imbalance removed by the current normalization step.
-/
noncomputable def availableWorkRN
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) : ℝ :=
  δ_relVol n T k - trajectoryRNBarrierNext n T k

/--
Heat-channel alias for the same one-step RN drop. A later owner surface may
split work and heat; this file currently proves only the conserved scalar drop.
-/
noncomputable def dissipatedHeatRN
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) : ℝ :=
  availableWorkRN n T k

theorem availableWorkRN_nonneg
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    0 ≤ availableWorkRN n T k := by
  unfold availableWorkRN
  exact sub_nonneg.mpr (δ_relVol_next_le (n := n) T k)

theorem dissipatedHeatRN_nonneg
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    0 ≤ dissipatedHeatRN n T k := by
  simpa [dissipatedHeatRN] using availableWorkRN_nonneg (n := n) T k

/--
Exact one-step RN balance: remaining RN barrier plus available work equals the
pre-step RN barrier.
-/
theorem trajectoryRNBarrierNext_add_availableWorkRN_eq_δ_relVol
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    trajectoryRNBarrierNext n T k + availableWorkRN n T k = δ_relVol n T k := by
  unfold availableWorkRN
  ring

/--
Equivalent heat-channel balance for the current scalar model.
-/
theorem trajectoryRNBarrierNext_add_dissipatedHeatRN_eq_δ_relVol
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) :
    trajectoryRNBarrierNext n T k + dissipatedHeatRN n T k = δ_relVol n T k := by
  simpa [dissipatedHeatRN] using
    trajectoryRNBarrierNext_add_availableWorkRN_eq_δ_relVol (n := n) T k

/--
Bridge from Sinkhorn relative-volume anomaly to the router odd-defect lane.
This is the owner surface for volume-driven defect reduction.
-/
structure SinkhornVolumeAnomalyBridge (n : Nat) where
  T : SinkhornTrajectory n
  state : Nat → RouterDefectBoundBridge (E := E)
  next_le_volumeNext :
    ∀ k : Nat, δ_odd (state (k + 1)) ≤ trajectoryRNBarrierNext n T k
  volume_le_now :
    ∀ k : Nat, trajectoryRNBarrier n T k ≤ δ_odd (state k)

/--
Primary-name alias: relative-defect bridge driven by trajectory RN barriers.
-/
abbrev SinkhornRelativeDefectBridge (n : Nat) :=
  SinkhornVolumeAnomalyBridge (E := E) n

/--
Thermodynamic bridge from Sinkhorn relative-volume anomaly to the corrected
router readout lane.

This is the non-legacy D3 owner surface: its states carry
`RouterDefectThermodynamicBridge`, and the defect readout is
`δ_odd_thermo`, not an ambient operator norm.
-/
structure SinkhornThermodynamicRelativeDefectBridge (n : Nat) where
  T : SinkhornTrajectory n
  state : Nat → RouterDefectThermodynamicBridge (E := E)
  next_le_volumeNext :
    ∀ k : Nat, δ_odd_thermo (state (k + 1)) ≤ trajectoryRNBarrierNext n T k
  volume_le_now :
    ∀ k : Nat, trajectoryRNBarrier n T k ≤ δ_odd_thermo (state k)

/--
Single-step RN-barrier comparison for the corrected thermodynamic D3 lane.

This structure does not identify the Sinkhorn RN barrier with
`relativeInformationNorm`. It records only the explicit scalar comparison
available in this owner file: the thermodynamic router readout is the current
RN barrier, and that barrier is below the thermodynamic `Z_D` readout budget.
-/
structure SinkhornRNBarrierThermodynamicComparison (n : Nat) where
  B : RouterDefectThermodynamicBridge (E := E)
  T : SinkhornTrajectory n
  k : Nat
  residual_readout_eq_barrier :
    δ_odd_thermo B = δ_relVol n T k
  central_readout_budget :
    δ_relVol n T k ≤ δ_ZD_thermo B

/--
Constructor that keeps the D3 budget theorem-backed once the current
thermodynamic residual readout has been identified with the current RN barrier.

This removes the need to supply the `central_readout_budget` field separately:
it is derived from `δ_odd_thermo_le_ZD` on the existing thermodynamic bridge.
-/
noncomputable def SinkhornRNBarrierThermodynamicComparison.ofResidualReadoutEqBarrier
    {n : Nat}
    (B : RouterDefectThermodynamicBridge (E := E))
    (T : SinkhornTrajectory n)
    (k : Nat)
    (hResidual : δ_odd_thermo B = δ_relVol n T k) :
    SinkhornRNBarrierThermodynamicComparison (E := E) n :=
  { B := B
    T := T
    k := k
    residual_readout_eq_barrier := hResidual
    central_readout_budget := by
      rw [← hResidual]
      exact δ_odd_thermo_le_ZD (E := E) B }

@[simp] theorem SinkhornRNBarrierThermodynamicComparison.ofResidualReadoutEqBarrier_central_readout_budget
    {n : Nat}
    (B : RouterDefectThermodynamicBridge (E := E))
    (T : SinkhornTrajectory n)
    (k : Nat)
    (hResidual : δ_odd_thermo B = δ_relVol n T k) :
    (SinkhornRNBarrierThermodynamicComparison.ofResidualReadoutEqBarrier
      (E := E) B T k hResidual).central_readout_budget =
      (by
        simpa [hResidual] using δ_odd_thermo_le_ZD (E := E) B) := by
  rfl

/--
An explicit RN-barrier comparison discharges the thermodynamic D3 bound.
-/
theorem δ_odd_thermo_le_ZD_of_rnBarrierComparison
    {n : Nat}
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n) :
    δ_odd_thermo C.B ≤ δ_ZD_thermo C.B := by
  rw [C.residual_readout_eq_barrier]
  exact C.central_readout_budget

/--
Exact remaining D3 profile-lift obligation.

The Sinkhorn RN barrier is an `L¹` sum of absolute logarithmic mass changes.
The matching projective readout in `RelativePotentialCore` is therefore
`informationGeometricRelativeNorm`, with an explicit finite-carrier scale
factor. This avoids forcing the RN barrier into the RMS
`relativeInformationNorm` lane before a separate comparison theorem exists.
-/
structure SinkhornRNBarrierProfileLift
    (n : Nat)
    (T : SinkhornTrajectory n)
    (k : Nat) where
  α : Type
  fintype : Fintype α
  nonempty : Nonempty α
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  defectRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  referenceRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  rnBarrier_eq_scaled_informationGeometricRelativeNorm :
    δ_relVol n T k =
      scale *
        @InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
          α fintype nonempty defectRay referenceRay

/--
Phase-local profile lift for the raw Sinkhorn RN barrier.

This is the row/column-local form of the remaining D3 lift. It avoids mentioning
trajectories and therefore isolates the actual construction problem: build the
positive-ray profile for `phaseRNBarrierBefore n phase M`.
-/
structure PhaseRNBarrierProfileLift
    (n : Nat)
    (phase : SinkhornPhase)
    (M : SinkhornMatrix n) where
  α : Type
  fintype : Fintype α
  nonempty : Nonempty α
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  defectRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  referenceRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  phaseRNBarrier_eq_scaled_informationGeometricRelativeNorm :
    phaseRNBarrierBefore n phase M =
      scale *
        @InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
          α fintype nonempty defectRay referenceRay

/-- Row-sum profile as observed positive count data. -/
noncomputable def rowSumCounts
    (n : Nat)
    (M : SinkhornMatrix n) :
    RelativeCounts n :=
  fun i => rowSum n M i

/-- Column-sum profile as observed positive count data. -/
noncomputable def colSumCounts
    (n : Nat)
    (M : SinkhornMatrix n) :
    RelativeCounts n :=
  fun j => colSum n M j

/-- Unit reference count profile on `Fin n`. -/
noncomputable def unitCounts (n : Nat) : RelativeCounts n :=
  fun _ => 1

theorem unitCounts_pos (n : Nat) :
    ∀ i : Fin n, 0 < unitCounts n i := by
  intro i
  simp [unitCounts]

theorem countMass_unitCounts
    (n : Nat)
    [Nonempty (Fin n)] :
    countMass (unitCounts n) (unitCounts_pos n) = n := by
  simp [countMass, unitCounts, positiveMeasureOfCounts, InfoGeometry.PositiveMeasure.Z]

/--
Row RN-barrier profile lift through positive observed count data.

The row sums are the observed positive counts. The explicit scale/equality field
keeps the unnormalized RN barrier separate from the projective count-ray
readout.
-/
structure RowRNBarrierCountProfileLift
    (n : Nat)
    [Nonempty (Fin n)]
    (M : SinkhornMatrix n)
    (hrow : HasPositiveRowSums n M) where
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  rowRNBarrier_eq_scaled_informationGeometricRelativeNorm :
    rowRNBarrier n M =
      scale *
        InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
          (countRay (unitCounts n) (unitCounts_pos n))
          (countRay (rowSumCounts n M) hrow)

/--
Column RN-barrier profile lift through positive observed count data.
-/
structure ColRNBarrierCountProfileLift
    (n : Nat)
    [Nonempty (Fin n)]
    (M : SinkhornMatrix n)
    (hcol : HasPositiveColSums n M) where
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  colRNBarrier_eq_scaled_informationGeometricRelativeNorm :
    colRNBarrier n M =
      scale *
        InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
          (countRay (unitCounts n) (unitCounts_pos n))
          (countRay (colSumCounts n M) hcol)

/--
Proof-carrying row-count mass-normalization witness for the RN-barrier profile
lift.

This packages the positivity and total-mass certificate needed to route a raw
row-count profile into the projective information-geometric readback lane.
-/
structure RowCountMassNormalizedWitness
    {n : Nat}
    [Nonempty (Fin n)]
    (M : SinkhornMatrix n) where
  hrow : HasPositiveRowSums n M
  hMass : countMass (rowSumCounts n M) hrow = n

/--
Construct the row RN-barrier profile lift from positive observed row counts
once the raw count profile has the expected carrier mass `n`.

The unit ray is the readout ray. This is forced by the definition of
`informationGeometricRelativeNorm`, which weights by its first argument; with
unit weights and row-count mass `n`, the scaled projective readout is exactly
the unweighted Sinkhorn RN barrier `∑ᵢ |log rowSumᵢ|`.
-/
noncomputable def RowRNBarrierCountProfileLift.ofMassNormalized
    {n : Nat}
    [Nonempty (Fin n)]
    {M : SinkhornMatrix n}
    (hrow : HasPositiveRowSums n M)
    (hMass : countMass (rowSumCounts n M) hrow = n) :
    RowRNBarrierCountProfileLift n M hrow :=
  { scale := n
    scale_nonneg := Nat.cast_nonneg n
    rowRNBarrier_eq_scaled_informationGeometricRelativeNorm := by
      unfold rowRNBarrier
      unfold InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hn_nat : 0 < n := by
        simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)›)
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast hn_nat
      have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
      have hunitMass :
          countMass (unitCounts n) (unitCounts_pos n) = n :=
        countMass_unitCounts n
      have hshift :
          countMassShift (unitCounts n) (rowSumCounts n M)
            (unitCounts_pos n) hrow = 0 := by
        rw [countMassShift_eq_neg_log_countRelativeVolumeChange]
        unfold countRelativeVolumeChange
        rw [hunitMass, hMass]
        simp [hn_ne]
      have hpot :
          InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential
              (countRay (unitCounts n) (unitCounts_pos n))
              (countRay (rowSumCounts n M) hrow) i
            = Real.log (rowSum n M i) := by
        rw [relativeModularPotential_countRay_eq_neg_relativeCountLogDensity_sub_massShift]
        rw [hshift, sub_zero]
        unfold relativeCountLogDensity relativeCountDensity rowSumCounts unitCounts
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (hrow i).ne']
        simp
      rw [gaugeSection_countRay_apply, hunitMass, unitCounts, hpot]
      field_simp [hn_ne] }

/--
Construct the column RN-barrier profile lift from positive observed column
counts once the raw count profile has the expected carrier mass `n`.
-/
noncomputable def ColRNBarrierCountProfileLift.ofMassNormalized
    {n : Nat}
    [Nonempty (Fin n)]
    {M : SinkhornMatrix n}
    (hcol : HasPositiveColSums n M)
    (hMass : countMass (colSumCounts n M) hcol = n) :
    ColRNBarrierCountProfileLift n M hcol :=
  { scale := n
    scale_nonneg := Nat.cast_nonneg n
    colRNBarrier_eq_scaled_informationGeometricRelativeNorm := by
      unfold colRNBarrier
      unfold InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hn_nat : 0 < n := by
        simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)›)
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast hn_nat
      have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
      have hunitMass :
          countMass (unitCounts n) (unitCounts_pos n) = n :=
        countMass_unitCounts n
      have hshift :
          countMassShift (unitCounts n) (colSumCounts n M)
            (unitCounts_pos n) hcol = 0 := by
        rw [countMassShift_eq_neg_log_countRelativeVolumeChange]
        unfold countRelativeVolumeChange
        rw [hunitMass, hMass]
        simp [hn_ne]
      have hpot :
          InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential
              (countRay (unitCounts n) (unitCounts_pos n))
              (countRay (colSumCounts n M) hcol) j
            = Real.log (colSum n M j) := by
        rw [relativeModularPotential_countRay_eq_neg_relativeCountLogDensity_sub_massShift]
        rw [hshift, sub_zero]
        unfold relativeCountLogDensity relativeCountDensity colSumCounts unitCounts
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (hcol j).ne']
        simp
      rw [gaugeSection_countRay_apply, hunitMass, unitCounts, hpot]
      field_simp [hn_ne] }

/--
Turn a row-count profile lift into the corresponding phase-local lift. The row
RN barrier is the pre-step phase barrier for a column-normalization step.
-/
noncomputable def PhaseRNBarrierProfileLift.ofRowCounts
    {n : Nat}
    [Nonempty (Fin n)]
    {M : SinkhornMatrix n}
    {hrow : HasPositiveRowSums n M}
    (L : RowRNBarrierCountProfileLift n M hrow) :
    PhaseRNBarrierProfileLift n SinkhornPhase.col M :=
  { α := Fin n
    fintype := inferInstance
    nonempty := inferInstance
    scale := L.scale
    scale_nonneg := L.scale_nonneg
    defectRay := countRay (unitCounts n) (unitCounts_pos n)
    referenceRay := countRay (rowSumCounts n M) hrow
    phaseRNBarrier_eq_scaled_informationGeometricRelativeNorm := by
      simpa [phaseRNBarrierBefore] using
        L.rowRNBarrier_eq_scaled_informationGeometricRelativeNorm }

/--
Turn a column-count profile lift into the corresponding phase-local lift. The
column RN barrier is the pre-step phase barrier for a row-normalization step.
-/
noncomputable def PhaseRNBarrierProfileLift.ofColCounts
    {n : Nat}
    [Nonempty (Fin n)]
    {M : SinkhornMatrix n}
    {hcol : HasPositiveColSums n M}
    (L : ColRNBarrierCountProfileLift n M hcol) :
    PhaseRNBarrierProfileLift n SinkhornPhase.row M :=
  { α := Fin n
    fintype := inferInstance
    nonempty := inferInstance
    scale := L.scale
    scale_nonneg := L.scale_nonneg
    defectRay := countRay (unitCounts n) (unitCounts_pos n)
    referenceRay := countRay (colSumCounts n M) hcol
    phaseRNBarrier_eq_scaled_informationGeometricRelativeNorm := by
      simpa [phaseRNBarrierBefore] using
        L.colRNBarrier_eq_scaled_informationGeometricRelativeNorm }

/--
A phase-local profile lift at `phaseAt k` gives the corresponding trajectory
RN-barrier profile lift.
-/
noncomputable def SinkhornRNBarrierProfileLift.ofPhase
    {n : Nat}
    {T : SinkhornTrajectory n}
    {k : Nat}
    (L : PhaseRNBarrierProfileLift n (phaseAt k) (T.state k)) :
    SinkhornRNBarrierProfileLift n T k :=
  { α := L.α
    fintype := L.fintype
    nonempty := L.nonempty
    scale := L.scale
    scale_nonneg := L.scale_nonneg
    defectRay := L.defectRay
    referenceRay := L.referenceRay
    rnBarrier_eq_scaled_informationGeometricRelativeNorm := by
      simpa [δ_relVol, trajectoryRNBarrier] using
        L.phaseRNBarrier_eq_scaled_informationGeometricRelativeNorm }

/--
If the current Sinkhorn phase is column-normalization, then a mass-normalized
row-count lift produces the trajectory-local RN-barrier profile lift directly.
-/
noncomputable def SinkhornRNBarrierProfileLift.ofMassNormalizedRowCounts
    {n : Nat}
    [Nonempty (Fin n)]
    {T : SinkhornTrajectory n}
    {k : Nat}
    (hk : phaseAt k = SinkhornPhase.col)
    {hrow : HasPositiveRowSums n (T.state k)}
    (hMass : countMass (rowSumCounts n (T.state k)) hrow = n) :
    SinkhornRNBarrierProfileLift n T k :=
  SinkhornRNBarrierProfileLift.ofPhase
    (T := T) (k := k)
    (hk.symm ▸
      PhaseRNBarrierProfileLift.ofRowCounts
        (RowRNBarrierCountProfileLift.ofMassNormalized
          (n := n) (M := T.state k) hrow hMass))

/--
Witness-routed row-count constructor for the trajectory-local RN-barrier
profile lift.

This narrows the explicit `hrow` / `hMass` pair to a single proof-carrying
mass-normalization witness.
-/
noncomputable def SinkhornRNBarrierProfileLift.ofRowCountMassNormalizedWitness
    {n : Nat}
    [Nonempty (Fin n)]
    {T : SinkhornTrajectory n}
    {k : Nat}
    (hk : phaseAt k = SinkhornPhase.col)
    (W : RowCountMassNormalizedWitness (M := T.state k)) :
    SinkhornRNBarrierProfileLift n T k :=
  SinkhornRNBarrierProfileLift.ofPhase
    (T := T) (k := k)
    (hk.symm ▸
      PhaseRNBarrierProfileLift.ofRowCounts
        (RowRNBarrierCountProfileLift.ofMassNormalized
          (n := n) (M := T.state k) W.hrow W.hMass))

/--
If the current Sinkhorn phase is row-normalization, then a mass-normalized
column-count lift produces the trajectory-local RN-barrier profile lift
directly.
-/
noncomputable def SinkhornRNBarrierProfileLift.ofMassNormalizedColCounts
    {n : Nat}
    [Nonempty (Fin n)]
    {T : SinkhornTrajectory n}
    {k : Nat}
    (hk : phaseAt k = SinkhornPhase.row)
    {hcol : HasPositiveColSums n (T.state k)}
    (hMass : countMass (colSumCounts n (T.state k)) hcol = n) :
    SinkhornRNBarrierProfileLift n T k :=
  SinkhornRNBarrierProfileLift.ofPhase
    (T := T) (k := k)
    (hk.symm ▸
      PhaseRNBarrierProfileLift.ofColCounts
        (ColRNBarrierCountProfileLift.ofMassNormalized
          (n := n) (M := T.state k) hcol hMass))

/--
If the remaining profile lift is supplied, the RN-barrier budget becomes a
repo-native projective modular-potential budget on the `L¹` readout lane.
-/
theorem scaled_informationGeometricRelativeNorm_le_ZD_of_rnBarrierProfileLift
    {n : Nat}
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (L : SinkhornRNBarrierProfileLift n C.T C.k) :
    L.scale *
        @InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
          L.α L.fintype L.nonempty L.defectRay L.referenceRay
      ≤ δ_ZD_thermo C.B := by
  rw [← L.rnBarrier_eq_scaled_informationGeometricRelativeNorm]
  exact C.central_readout_budget

/--
Concrete profile-level Weyl/thermodynamic packet derived from Sinkhorn RN
barrier data.

The residual readout is identified with the scaled projective count/profile
readout supplied by `SinkhornRNBarrierProfileLift`. The central readout remains
the same scalar budget already present in the thermodynamic bridge. This does
not assert an RMS `relativeInformationNorm` identity.
-/
noncomputable def WeylThermodynamicProfileComparison.ofSinkhornRNBarrier
    {n : Nat}
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (L : SinkhornRNBarrierProfileLift n C.T C.k) :
    WeylThermodynamicProfileComparison (E := E)
      C.B.routerResidual
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) :=
  { α := L.α
    fintype := L.fintype
    nonempty := L.nonempty
    operatorInformationNormReadout := C.B.comparison.operatorInformationNormReadout
    defectScale := L.scale
    defectScale_nonneg := L.scale_nonneg
    defectRay := L.defectRay
    referenceRay := L.referenceRay
    residual_readout_eq_scaled_informationGeometricRelativeNorm := by
      rw [← L.rnBarrier_eq_scaled_informationGeometricRelativeNorm]
      exact C.residual_readout_eq_barrier
    scaled_informationGeometricRelativeNorm_le_central_readout := by
      rw [← L.rnBarrier_eq_scaled_informationGeometricRelativeNorm]
      simpa [δ_ZD_thermo] using C.central_readout_budget }

/--
Mass-normalized row counts at a column-normalization phase directly package the
Sinkhorn RN budget as a profile Weyl/thermodynamic comparison packet.
-/
noncomputable def WeylThermodynamicProfileComparison.ofMassNormalizedRowCounts
    {n : Nat}
    [Nonempty (Fin n)]
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (hk : phaseAt C.k = SinkhornPhase.col)
    {hrow : HasPositiveRowSums n (C.T.state C.k)}
    (hMass : countMass (rowSumCounts n (C.T.state C.k)) hrow = n) :
    WeylThermodynamicProfileComparison (E := E)
      C.B.routerResidual
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) :=
  WeylThermodynamicProfileComparison.ofSinkhornRNBarrier (E := E) C
    (SinkhornRNBarrierProfileLift.ofMassNormalizedRowCounts
      (T := C.T) (k := C.k) hk hMass)

/--
Witness-routed row-count constructor for the profile Weyl/thermodynamic
comparison packet.
-/
noncomputable def WeylThermodynamicProfileComparison.ofRowCountMassNormalizedWitness
    {n : Nat}
    [Nonempty (Fin n)]
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (hk : phaseAt C.k = SinkhornPhase.col)
    (W : RowCountMassNormalizedWitness (M := C.T.state C.k)) :
    WeylThermodynamicProfileComparison (E := E)
      C.B.routerResidual
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) :=
  WeylThermodynamicProfileComparison.ofSinkhornRNBarrier (E := E) C
    (SinkhornRNBarrierProfileLift.ofRowCountMassNormalizedWitness
      (T := C.T) (k := C.k) hk W)

/--
Mass-normalized column counts at a row-normalization phase directly package the
Sinkhorn RN budget as a profile Weyl/thermodynamic comparison packet.
-/
noncomputable def WeylThermodynamicProfileComparison.ofMassNormalizedColCounts
    {n : Nat}
    [Nonempty (Fin n)]
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (hk : phaseAt C.k = SinkhornPhase.row)
    {hcol : HasPositiveColSums n (C.T.state C.k)}
    (hMass : countMass (colSumCounts n (C.T.state C.k)) hcol = n) :
    WeylThermodynamicProfileComparison (E := E)
      C.B.routerResidual
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) :=
  WeylThermodynamicProfileComparison.ofSinkhornRNBarrier (E := E) C
    (SinkhornRNBarrierProfileLift.ofMassNormalizedColCounts
      (T := C.T) (k := C.k) hk hMass)

/--
The Sinkhorn-derived profile comparison gives the corrected readout inequality.
-/
theorem operatorInformationNormReadout_le_of_sinkhornRNBarrierProfile
    {n : Nat}
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (L : SinkhornRNBarrierProfileLift n C.T C.k) :
    C.B.comparison.operatorInformationNormReadout C.B.routerResidual
      ≤
    C.B.comparison.operatorInformationNormReadout
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) :=
  RouterDefectBoundBridge.operatorInformationNormReadout_le_of_weylThermodynamicProfileComparison
    (E := E)
    (WeylThermodynamicProfileComparison.ofSinkhornRNBarrier (E := E) C L)

/--
Mass-normalized row counts at a column-normalization phase are enough to route
the Sinkhorn RN budget all the way to the operator readout inequality.
-/
theorem operatorInformationNormReadout_le_of_massNormalizedRowCounts
    {n : Nat}
    [Nonempty (Fin n)]
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (hk : phaseAt C.k = SinkhornPhase.col)
    {hrow : HasPositiveRowSums n (C.T.state C.k)}
    (hMass : countMass (rowSumCounts n (C.T.state C.k)) hrow = n) :
    C.B.comparison.operatorInformationNormReadout C.B.routerResidual
      ≤
    C.B.comparison.operatorInformationNormReadout
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) := by
  exact
    RouterDefectBoundBridge.operatorInformationNormReadout_le_of_weylThermodynamicProfileComparison
      (E := E)
      (WeylThermodynamicProfileComparison.ofMassNormalizedRowCounts
        (E := E) C hk hMass)

/--
Witness-routed row-count mass-normalization is enough to derive the operator
readout inequality.
-/
theorem operatorInformationNormReadout_le_of_rowCountMassNormalizedWitness
    {n : Nat}
    [Nonempty (Fin n)]
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (hk : phaseAt C.k = SinkhornPhase.col)
    (W : RowCountMassNormalizedWitness (M := C.T.state C.k)) :
    C.B.comparison.operatorInformationNormReadout C.B.routerResidual
      ≤
    C.B.comparison.operatorInformationNormReadout
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) := by
  exact
    RouterDefectBoundBridge.operatorInformationNormReadout_le_of_weylThermodynamicProfileComparison
      (E := E)
      (WeylThermodynamicProfileComparison.ofRowCountMassNormalizedWitness
        (E := E) C hk W)

/--
Mass-normalized column counts at a row-normalization phase are enough to route
the Sinkhorn RN budget all the way to the operator readout inequality.
-/
theorem operatorInformationNormReadout_le_of_massNormalizedColCounts
    {n : Nat}
    [Nonempty (Fin n)]
    (C : SinkhornRNBarrierThermodynamicComparison (E := E) n)
    (hk : phaseAt C.k = SinkhornPhase.row)
    {hcol : HasPositiveColSums n (C.T.state C.k)}
    (hMass : countMass (colSumCounts n (C.T.state C.k)) hcol = n) :
    C.B.comparison.operatorInformationNormReadout C.B.routerResidual
      ≤
    C.B.comparison.operatorInformationNormReadout
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) C.B.CIK) := by
  exact
    RouterDefectBoundBridge.operatorInformationNormReadout_le_of_weylThermodynamicProfileComparison
      (E := E)
      (WeylThermodynamicProfileComparison.ofMassNormalizedColCounts
        (E := E) C hk hMass)

/--
Volume anomaly monotonicity forces one-step odd-defect monotonicity.
-/
theorem δ_odd_next_le_of_relativeDefectBridge
    {n : Nat}
    (B : SinkhornRelativeDefectBridge (E := E) n)
    (k : Nat) :
    δ_odd (B.state (k + 1)) ≤ δ_odd (B.state k) := by
  exact le_trans (B.next_le_volumeNext k)
    (le_trans (trajectoryRNBarrier_monotone (n := n) B.T k) (B.volume_le_now k))

/--
Backward-compatible theorem name for relative-defect one-step reduction.
-/
theorem δ_odd_next_le_of_volumeAnomalyBridge
    {n : Nat}
    (B : SinkhornVolumeAnomalyBridge (E := E) n)
    (k : Nat) :
    δ_odd (B.state (k + 1)) ≤ δ_odd (B.state k) :=
  δ_odd_next_le_of_relativeDefectBridge (E := E) B k

/--
RN-barrier monotonicity forces one-step thermodynamic odd-readout reduction.
-/
theorem δ_odd_thermo_next_le_of_relativeDefectBridge
    {n : Nat}
    (B : SinkhornThermodynamicRelativeDefectBridge (E := E) n)
    (k : Nat) :
    δ_odd_thermo (B.state (k + 1)) ≤ δ_odd_thermo (B.state k) := by
  exact le_trans (B.next_le_volumeNext k)
    (le_trans (trajectoryRNBarrier_monotone (n := n) B.T k) (B.volume_le_now k))

/--
One-step thermodynamic D3 budget transport: if the current RN barrier is below
the current thermodynamic `Z_D` readout, then the next router readout is also
below that same current budget.
-/
theorem δ_odd_thermo_next_le_ZD_of_relativeDefectBridge
    {n : Nat}
    (B : SinkhornThermodynamicRelativeDefectBridge (E := E) n)
    (k : Nat)
    (hBudget : δ_relVol n B.T k ≤ δ_ZD_thermo (B.state k)) :
    δ_odd_thermo (B.state (k + 1)) ≤ δ_ZD_thermo (B.state k) := by
  exact le_trans (B.next_le_volumeNext k)
    (le_trans (δ_relVol_next_le (n := n) B.T k) hBudget)

end VolumeAnomaly

end InfoGeometry.LLM.SinkhornDefectFlow

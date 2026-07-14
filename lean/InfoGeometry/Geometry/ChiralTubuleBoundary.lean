/-
InfoGeometry/Geometry/ChiralTubuleBoundary.lean

Chiral tubule phase-transition boundary.

This module formalizes the snap boundary where regular Bregman/Legendre
geometry loses Hessian invertibility and a chiral phase-separation witness
appears.

The module does not assert that high temperature alone creates a tubule.
Temperature, shear, Hessian degeneracy, and residue formation are connected
only through proof-carrying calibration data.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.TopologicalSnap
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace ChiralTubuleBoundary

open InfoGeometry.OperatorAlgebra.TopologicalSnap

/-! ## 1. Bregman Hessian degeneracy -/

/--
Bregman/Fenchel Hessian data.

`isInvertibleAt U` is the regularity predicate for the local Legendre/Fisher
Hessian at `U`.
-/
structure BregmanHessianDatum
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  /-- Hessian/response operator at a state. -/
  hessian : Op → (Op →L[ℝ] Op)

  /-- Regularity predicate for the Hessian. -/
  isInvertibleAt : Op → Prop

/--
The topological snap boundary is the locus where the Hessian ceases to be
invertible.
-/
def IsTopologicalSnapBoundary
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (H : BregmanHessianDatum Op)
    (U : Op) : Prop :=
  ¬ H.isInvertibleAt U

/-! ## 2. Dual-flat shear and extreme-shear threshold -/

/--
Dual-flat operator geometry.

`nablaExp` and `nablaMix` represent the exponential and mixture connections.
Their difference is the Amari-Chentsov/Bregman shear operator.
-/
structure DualFlatOperatorGeometry
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op] where
  nablaExp : Op → (Op →L[ℝ] Op)
  nablaMix : Op → (Op →L[ℝ] Op)

/-- Amari-Chentsov shear operator. -/
def torsionShear
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (G : DualFlatOperatorGeometry Op)
    (U : Op) : Op →L[ℝ] Op :=
  G.nablaExp U - G.nablaMix U

/-- Real-valued shear magnitude. -/
def shearMagnitude
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (G : DualFlatOperatorGeometry Op)
    (U : Op) : ℝ :=
  ‖torsionShear G U‖

/--
Threshold version of extreme shear.

This replaces invalid expressions such as `‖torsion‖ = ∞`.
-/
def IsExtremeShear
    {Op : Type*} [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (G : DualFlatOperatorGeometry Op)
    (threshold : ℝ)
    (U : Op) : Prop :=
  threshold ≤ shearMagnitude G U

/-! ## 3. Thermal drive calibration -/

/--
Thermal drive datum.

This is where an Unruh, Hawking, or material-temperature readout can be
connected to the Bregman shear.  The temperature does not itself define the
snap; it is calibrated into a shear threshold.
-/
structure ThermalDriveDatum
    (Op : Type*) where
  /-- Temperature or effective thermal drive readout. -/
  temperature : Op → ℝ

  /-- Critical temperature/readout. -/
  criticalTemperature : ℝ

/--
The state is thermally critical when its calibrated thermal drive exceeds the
critical threshold.
-/
def IsThermallyCritical
    {Op : Type*}
    (T : ThermalDriveDatum Op)
    (U : Op) : Prop :=
  T.criticalTemperature ≤ T.temperature U

/--
A calibration saying thermal criticality forces extreme Bregman shear.

This is the precise place where a statement such as "Unruh temperature is high
enough to trigger the snap" belongs.
-/
structure ThermalShearCalibration
    (Op : Type*) [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    (G : DualFlatOperatorGeometry Op)
    (T : ThermalDriveDatum Op) where
  /-- Shear threshold. -/
  shearThreshold : ℝ

  /-- The threshold is nonnegative. -/
  shearThreshold_nonneg : 0 ≤ shearThreshold

  /-- Thermal criticality implies extreme Bregman shear. -/
  thermal_critical_implies_extreme_shear :
    ∀ U : Op,
      IsThermallyCritical T U →
        IsExtremeShear G shearThreshold U

/-! ## 4. Majorana-Weyl residue socket -/

/--
A stable chiral residue created at a snap boundary.

The certificates are intentionally proof-carrying because Majorana/Weyl
conditions depend on signature, dimension, representation, and real structure.
-/
structure MajoranaWeylResidueDatum
    (Charge Residue : Type*) [Zero Charge] where
  /-- The produced residue object. -/
  residue : Residue

  /-- Topological/anomaly charge carried by the residue. -/
  charge : Charge

  /-- The residue is topologically nontrivial. -/
  charge_nonzero : charge ≠ 0

/-! ## 5. Chiral tubule crystallization -/

/--
A chiral tubule crystallization witness.

At a snap boundary, the regular phase separates into two disjoint chiral phases
and produces a nontrivial residue.
-/
structure ChiralTubuleCrystallization
    (Op Charge Residue : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge]
    (H : BregmanHessianDatum Op) where
  /-- Boundary state where the snap occurs. -/
  boundaryState : Op

  /-- The boundary state lies on the Hessian-degeneracy locus. -/
  is_snap :
    IsTopologicalSnapBoundary H boundaryState

  /-- Right/system chiral phase. -/
  phaseR : Set Op

  /-- Left/commutant chiral phase. -/
  phaseL : Set Op

  /-- The two phases are separated. -/
  phase_disjoint :
    Disjoint phaseR phaseL

  /-- Stable residue generated at the boundary. -/
  residue :
    MajoranaWeylResidueDatum Charge Residue

namespace ChiralTubuleCrystallization

variable
    {Op Charge Residue : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge]
    {H : BregmanHessianDatum Op}

/-- The two chiral phases are disjoint. -/
theorem disjoint_phases
    (C : ChiralTubuleCrystallization Op Charge Residue H) :
    Disjoint C.phaseR C.phaseL :=
  C.phase_disjoint

/-- The produced residue has nontrivial charge. -/
theorem residue_charge_nonzero
    (C : ChiralTubuleCrystallization Op Charge Residue H) :
    C.residue.charge ≠ 0 :=
  C.residue.charge_nonzero

end ChiralTubuleCrystallization

/-! ## 6. Transition law -/

/--
Transition law saying that snap-boundary plus extreme shear plus thermal drive
forces chiral tubule crystallization.

This is a physical/geometric bridge witness, not a theorem derivable from
abstract Hessian data alone.
-/
structure ChiralTubuleTransitionLaw
    (Op Charge Residue : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge]
    (H : BregmanHessianDatum Op)
    (G : DualFlatOperatorGeometry Op)
    (T : ThermalDriveDatum Op) where
  /-- Shear threshold. -/
  threshold : ℝ

  /-- The threshold is nonnegative. -/
  threshold_nonneg : 0 ≤ threshold

  /--
  Transition law: at a Hessian-degenerate snap boundary, extreme shear and
  thermal criticality generate a chiral tubule crystallization.
  -/
  snap_transition :
    ∀ U : Op,
      IsTopologicalSnapBoundary H U →
      IsExtremeShear G threshold U →
      IsThermallyCritical T U →
        ∃ C : ChiralTubuleCrystallization Op Charge Residue H,
          C.boundaryState = U

namespace ChiralTubuleTransitionLaw

variable
    {Op Charge Residue : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge]
    {H : BregmanHessianDatum Op}
    {G : DualFlatOperatorGeometry Op}
    {T : ThermalDriveDatum Op}

/--
A snap boundary with extreme shear and thermal criticality yields a chiral
tubule crystallization once the transition law is supplied.
-/
theorem snap_implies_crystallization
    (L : ChiralTubuleTransitionLaw Op Charge Residue H G T)
    (U : Op)
    (hSnap : IsTopologicalSnapBoundary H U)
    (hShear : IsExtremeShear G L.threshold U)
    (hThermal : IsThermallyCritical T U) :
    ∃ C : ChiralTubuleCrystallization Op Charge Residue H,
      C.boundaryState = U :=
  L.snap_transition U hSnap hShear hThermal

end ChiralTubuleTransitionLaw

/-! ## 7. Thermal-triggered transition via calibration -/

/--
A calibrated transition law using thermal drive to imply the shear threshold.

This packages the statement:

  thermal criticality
    → extreme shear
    → snap transition.
-/
structure ThermalTriggeredTubuleLaw
    (Op Charge Residue : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge]
    (H : BregmanHessianDatum Op)
    (G : DualFlatOperatorGeometry Op)
    (T : ThermalDriveDatum Op) where
  shearCalibration :
    ThermalShearCalibration Op G T

  transitionLaw :
    ChiralTubuleTransitionLaw
      Op Charge Residue H G T

  /-- The transition law threshold agrees with the calibrated shear threshold. -/
  threshold_agrees :
    transitionLaw.threshold = shearCalibration.shearThreshold

namespace ThermalTriggeredTubuleLaw

variable
    {Op Charge Residue : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge]
    {H : BregmanHessianDatum Op}
    {G : DualFlatOperatorGeometry Op}
    {T : ThermalDriveDatum Op}

/--
Thermal criticality plus Hessian snap boundary yields chiral tubule
crystallization, once the calibration and transition law are supplied.
-/
theorem thermal_snap_implies_crystallization
    (L : ThermalTriggeredTubuleLaw Op Charge Residue H G T)
    (U : Op)
    (hSnap : IsTopologicalSnapBoundary H U)
    (hThermal : IsThermallyCritical T U) :
    ∃ C : ChiralTubuleCrystallization Op Charge Residue H,
      C.boundaryState = U := by
  have hShear :
      IsExtremeShear G L.transitionLaw.threshold U := by
    rw [L.threshold_agrees]
    exact L.shearCalibration.thermal_critical_implies_extreme_shear U hThermal
  exact L.transitionLaw.snap_implies_crystallization
    U hSnap hShear hThermal

end ThermalTriggeredTubuleLaw

/-! ## 8. Protection after the snap -/

/--
A snapped tubule sector protected by a conserved obstruction flow.

This is the connection to `TopologicalSnap`: after the nontrivial residue is
present, it cannot relax into the flat sector under an invariant-preserving
flow.
-/
structure ProtectedTubuleSector
    (State Charge : Type*) [Zero Charge] where
  obstructionFlow :
    ConservedObstructionFlow State Charge

  tubuleState : State

  /-- The tubule carries nontrivial obstruction. -/
  tubule_nontrivial :
    obstructionFlow.invariant tubuleState ≠ 0

namespace ProtectedTubuleSector

variable {State Charge : Type*} [Zero Charge]
variable (P : ProtectedTubuleSector State Charge)

/--
A protected tubule cannot flow to the flat sector at any admissible time.
-/
theorem cannot_relax_to_flat
    (t : ℝ) :
    P.obstructionFlow.flow t P.tubuleState ∉ P.obstructionFlow.Flat :=
  P.obstructionFlow.nontrivial_cannot_flow_to_flat
    P.tubule_nontrivial t

end ProtectedTubuleSector

/-! ## 9. Boundary readout -/

/--
Chiral tubule boundary readout.

It is intentionally witness-gated by thermal/shear calibration and a transition
law.
-/
theorem chiralTubuleBoundaryOwnerTarget :
  ∀ (Op Charge Residue : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge],
  ∀ H : BregmanHessianDatum Op,
  ∀ G : DualFlatOperatorGeometry Op,
  ∀ T : ThermalDriveDatum Op,
  ∀ _L : ThermalTriggeredTubuleLaw Op Charge Residue H G T,
  ∀ U : Op,
    IsTopologicalSnapBoundary H U →
    IsThermallyCritical T U →
      ∃ C : ChiralTubuleCrystallization Op Charge Residue H,
        C.boundaryState = U := by
  intro Op Charge Residue _ _ _ H G T L U hSnap hThermal
  exact L.thermal_snap_implies_crystallization U hSnap hThermal

/-- Packet readout for one thermally triggered chiral tubule boundary. -/
theorem chiralTubuleBoundary_packet
    (Op Charge Residue : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [Zero Charge]
    (H : BregmanHessianDatum Op)
    (G : DualFlatOperatorGeometry Op)
    (T : ThermalDriveDatum Op)
    (L : ThermalTriggeredTubuleLaw Op Charge Residue H G T)
    (U : Op)
    (hSnap : IsTopologicalSnapBoundary H U)
    (hThermal : IsThermallyCritical T U) :
    ∃ C : ChiralTubuleCrystallization Op Charge Residue H,
      C.boundaryState = U :=
  chiralTubuleBoundaryOwnerTarget Op Charge Residue H G T L U hSnap hThermal

end ChiralTubuleBoundary

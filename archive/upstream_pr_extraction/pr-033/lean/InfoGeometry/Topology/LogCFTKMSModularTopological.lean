import Mathlib
import InfoGeometry.Physics.Thermodynamics.LogCFTKMSModularTriple

/-!
# Topological logarithmic CFT KMS readout

This owner packages the continuity of the already-verified unipotent/logarithmic
KMS flow on bounded operators.  It does not introduce a new KMS state or a
Tomita--Takesaki theorem.
-/

namespace InfoGeometry.Topology.LogCFTKMSModularTopological

open ContinuousLinearMap
open InfoGeometry.Physics.Algebra
open InfoGeometry.Physics.Thermodynamics
open InfoGeometry.Physics.Thermodynamics.TopologicalMonodromyKMSBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

local notation "EndH" => H →L[ℝ] H

local instance : AddCommGroup EndH := inferInstance
local instance : Module ℝ EndH := inferInstance
noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- The logarithmic KMS readout flow as a continuous map on the operator carrier. -/
def logCFTKMSReadoutFlow
    (M : ContinuousMonodromyOperator H)
    (hM : ContinuousMonodromyOperatorLaws M) :
    ℝ × EndH → EndH :=
  fun p => (unipotentMonodromyReadoutDatum M hM).flow p.1 p.2

/-- The logarithmic KMS readout flow is continuous. -/
theorem continuous_logCFTKMSReadoutFlow
    (M : ContinuousMonodromyOperator H)
    (hM : ContinuousMonodromyOperatorLaws M) :
    Continuous (logCFTKMSReadoutFlow M hM) := by
  unfold logCFTKMSReadoutFlow
  have hflow : Continuous (fun p : ℝ × EndH =>
      continuousUnipotentFlow M p.1) :=
    (continuous_continuousUnipotentFlow (M := M)).comp continuous_fst
  simpa using hflow.mul continuous_snd

@[simp] theorem logCFTKMSReadoutFlow_apply
    (M : ContinuousMonodromyOperator H) (t : ℝ) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    logCFTKMSReadoutFlow M hM (t, T) =
      (unipotentMonodromyReadoutDatum M hM).flow t T :=
  rfl

@[simp] theorem logCFTKMSReadoutFlow_zero
    (M : ContinuousMonodromyOperator H) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    logCFTKMSReadoutFlow M hM (0, T) = T := by
  simpa [logCFTKMSReadoutFlow] using
    (unipotentMonodromyReadoutDatum (H := H) M hM).flow_zero T

theorem logCFTKMSReadoutFlow_add
    (M : ContinuousMonodromyOperator H) (s t : ℝ) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    logCFTKMSReadoutFlow M hM (s + t, T) =
      logCFTKMSReadoutFlow M hM (s, logCFTKMSReadoutFlow M hM (t, T)) := by
  simpa [logCFTKMSReadoutFlow] using
    (unipotentMonodromyReadoutDatum (H := H) M hM).flow_add s t T

@[simp] theorem logCFTKMSCanonical_flow_zero
    (M : ContinuousMonodromyOperator H) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    (logCFTKMSCanonical (H := H) M hM).readout.flow 0 T = T := by
  simpa using
    (logCFTKMS_flow_zero (T := logCFTKMSCanonical (H := H) M hM) T)

theorem logCFTKMSCanonical_flow_add
    (M : ContinuousMonodromyOperator H) (s t : ℝ) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    (logCFTKMSCanonical (H := H) M hM).readout.flow (s + t) T =
      (logCFTKMSCanonical (H := H) M hM).readout.flow s
        ((logCFTKMSCanonical (H := H) M hM).readout.flow t T) := by
  simpa using
    (logCFTKMS_flow_add (T := logCFTKMSCanonical (H := H) M hM) s t T)

theorem logCFTKMSCanonical_flow_invariant
    (M : ContinuousMonodromyOperator H) (t : ℝ) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    (logCFTKMSCanonical (H := H) M hM).readout.state
      ((logCFTKMSCanonical (H := H) M hM).readout.flow t T) =
      (logCFTKMSCanonical (H := H) M hM).readout.state T := by
  simpa using
    (logCFTKMS_flow_invariant (T := logCFTKMSCanonical (H := H) M hM) t T)

/--
The canonical logarithmic CFT readout flow at fixed time is a homeomorphism
on the bounded-operator carrier.
-/
noncomputable def logCFTKMSCanonical_flowHomeomorph
    (M : ContinuousMonodromyOperator H) (t : ℝ)
    (hM : ContinuousMonodromyOperatorLaws M) :
    EndH ≃ₜ EndH :=
  (InfoGeometry.Physics.Thermodynamics.logCFTKMSCanonical_flowEquiv
    (H := H) M t hM).toHomeomorph

@[simp] theorem logCFTKMSCanonical_flowHomeomorph_apply
    (M : ContinuousMonodromyOperator H) (t : ℝ) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    logCFTKMSCanonical_flowHomeomorph (H := H) M t hM T =
      (logCFTKMSCanonical (H := H) M hM).readout.flow t T :=
  rfl

@[simp] theorem logCFTKMSCanonical_flowHomeomorph_symm_apply
    (M : ContinuousMonodromyOperator H) (t : ℝ) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    (logCFTKMSCanonical_flowHomeomorph (H := H) M t hM).symm T =
      (logCFTKMSCanonical (H := H) M hM).readout.flow (-t) T :=
  rfl

@[simp] theorem logCFTKMSCanonical_flowHomeomorph_zero_apply
    (M : ContinuousMonodromyOperator H) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    logCFTKMSCanonical_flowHomeomorph (H := H) M 0 hM T = T := by
  simpa using (logCFTKMSCanonical_flow_zero (H := H) M T hM)

theorem logCFTKMSCanonical_flowHomeomorph_add_apply
    (M : ContinuousMonodromyOperator H) (s t : ℝ) (T : EndH)
    (hM : ContinuousMonodromyOperatorLaws M) :
    logCFTKMSCanonical_flowHomeomorph (H := H) M (s + t) hM T =
      logCFTKMSCanonical_flowHomeomorph (H := H) M s hM
        (logCFTKMSCanonical_flowHomeomorph (H := H) M t hM T) := by
  simpa using (logCFTKMSCanonical_flow_add (H := H) M s t T hM)

theorem logCFTKMSCanonical_flowHomeomorph_comp
    (M : ContinuousMonodromyOperator H) (s t : ℝ)
    (hM : ContinuousMonodromyOperatorLaws M) :
    (logCFTKMSCanonical_flowHomeomorph (H := H) M t hM).trans
        (logCFTKMSCanonical_flowHomeomorph (H := H) M s hM) =
      logCFTKMSCanonical_flowHomeomorph (H := H) M (t + s) hM := by
  ext T x
  have h := logCFTKMS_flow_add (T := logCFTKMSCanonical (H := H) M hM) s t T
  simpa [add_comm] using congrArg (fun Y : EndH => Y x) h.symm

@[simp] theorem logCFTKMSCanonical_flowHomeomorph_comp_neg
    (M : ContinuousMonodromyOperator H) (t : ℝ)
    (hM : ContinuousMonodromyOperatorLaws M) :
    (logCFTKMSCanonical_flowHomeomorph (H := H) M t hM).trans
        (logCFTKMSCanonical_flowHomeomorph (H := H) M (-t) hM) =
      Homeomorph.refl _ := by
  ext T x
  have h₀ :
      ((logCFTKMSCanonical_flowHomeomorph (H := H) M (-t) hM)
          (logCFTKMSCanonical_flowHomeomorph (H := H) M t hM T)) x =
        T x := by
    have h := logCFTKMSCanonical_flowHomeomorph_add_apply (H := H) M (-t) t T hM
    have hzero :
        ((logCFTKMSCanonical_flowHomeomorph (H := H) M 0 hM) T) x = T x := by
      simpa using congrArg (fun Y : EndH => Y x)
        (logCFTKMSCanonical_flowHomeomorph_zero_apply (H := H) M T hM)
    have hstep :
        ((logCFTKMSCanonical_flowHomeomorph (H := H) M (-t) hM)
            (logCFTKMSCanonical_flowHomeomorph (H := H) M t hM T)) x =
          ((logCFTKMSCanonical_flowHomeomorph (H := H) M 0 hM) T) x := by
      simpa [add_comm, add_left_comm, add_assoc] using
        congrArg (fun Y : EndH => Y x) h.symm
    exact hstep.trans hzero
  simpa [Homeomorph.trans] using h₀

end

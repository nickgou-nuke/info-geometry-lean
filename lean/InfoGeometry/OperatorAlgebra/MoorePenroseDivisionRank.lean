import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional

/-!
# InfoGeometry.OperatorAlgebra.MoorePenroseDivisionRank

Conditional calibration tying the Drazin stable volume to the metric rank
or trace of a Moore--Penrose projector.

This module does not prove Moore--Penrose existence, trace-class properties,
division-algebra classification, semisimplicity, or rank/trace theorems. It
records the exact bridge needed by downstream finite/localized models:

* stable Drazin volume is read by a trace of an MP projector;
* division/localized-fiber hypotheses supply `trace >= 1`;
* therefore calibrated Drazin entropy is nonnegative.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MoorePenroseDivisionRank

/--
Calibration linking the Drazin stable volume to a Moore--Penrose projector
trace/rank readout.

The intended projector is `A⁺ * A` or `A * A⁺`, depending on the chosen metric
side. This file does not choose the side; it only records the calibrated
readout.
-/
structure MoorePenroseVolumeCalibration (Op State : Type*) where
  /-- The underlying Drazin-stable entropy calibration. -/
  functional : DrazinEntropyFunctional Op State
  /-- The Moore--Penrose projector assigned to the state. -/
  mpProjector : State -> Op
  /-- Trace/rank/readout functional on the operator algebra. -/
  trace : Op -> ℝ
  /-- Core metric link: Drazin stable volume equals trace of the MP projector. -/
  volume_eq_mp_trace :
    ∀ s : State, functional.readout.valid s ->
      functional.readout.stableVolume s = trace (mpProjector s)

namespace MoorePenroseVolumeCalibration

variable {Op State : Type*}
variable (C : MoorePenroseVolumeCalibration Op State)

/-- Entropy expressed through the Moore--Penrose trace/rank readout. -/
theorem entropy_eq_log_mp_trace
    (s : State) (hs : C.functional.readout.valid s) :
    C.functional.entropy s =
      C.functional.kB * Real.log (C.trace (C.mpProjector s)) := by
  calc
    C.functional.entropy s
        = C.functional.kB * Real.log (C.functional.readout.stableVolume s) :=
            C.functional.entropy_eq_kB_log_volume s hs
    _ = C.functional.kB * Real.log (C.trace (C.mpProjector s)) := by
            rw [C.volume_eq_mp_trace s hs]

/-- If the MP trace/rank readout is at least one, entropy is nonnegative. -/
theorem entropy_nonneg_of_one_le_mp_trace
    (s : State) (hs : C.functional.readout.valid s)
    (htrace : 1 ≤ C.trace (C.mpProjector s)) :
    0 ≤ C.functional.entropy s := by
  have hvol : 1 ≤ C.functional.readout.stableVolume s := by
    rw [C.volume_eq_mp_trace s hs]
    exact htrace
  exact C.functional.entropy_nonneg_of_one_le_stableVolume s hs hvol

end MoorePenroseVolumeCalibration

/--
A faithful dimension-trace calibration on division fibers.

This is the minimal trace socket needed for the division-fiber argument: the
identity element of a nontrivial division block has trace/rank at least one.
-/
structure FaithfulDivisionTraceLaw (Op State : Type*) where
  /-- Trace/rank/readout functional. -/
  trace : Op -> ℝ
  /-- Predicate that a state has localized to a division-algebra fiber. -/
  isDivisionAlgebraFiber : State -> Prop
  /-- The division fiber is represented nontrivially on the metric/operator carrier. -/
  representedNontrivially : State -> Prop
  /-- Identity element of the localized division block attached to a state. -/
  identityOf : State -> Op
  /-- Faithfulness/dimension lower bound on division-fiber identities. -/
  trace_identity_ge_one :
    ∀ s : State, isDivisionAlgebraFiber s ->
      representedNontrivially s -> 1 ≤ trace (identityOf s)

/--
Moore--Penrose projector identity law on division fibers.

This packages the concrete division-algebra step: on a valid division fiber,
the Moore--Penrose projector is the identity of that localized block. Together
with a faithful trace law, this derives the `trace >= 1` bound used by the DIII
entropy bridge.
-/
structure MoorePenroseDivisionIdentityLaw (Op State : Type*) where
  /-- MP trace/rank calibration for the same entropy functional. -/
  calibration : MoorePenroseVolumeCalibration Op State
  /-- Faithful trace law on division-fiber identities. -/
  faithfulTrace : FaithfulDivisionTraceLaw Op State
  /-- The faithful trace is the calibration trace. -/
  faithfulTrace_trace_eq :
    faithfulTrace.trace = calibration.trace
  /--
  On a valid division fiber, the Moore--Penrose projector is the identity of
  the localized division block.
  -/
  mpProjector_eq_identity_of_division :
    ∀ s : State, calibration.functional.readout.valid s ->
      faithfulTrace.isDivisionAlgebraFiber s ->
      faithfulTrace.representedNontrivially s ->
      calibration.mpProjector s = faithfulTrace.identityOf s

namespace MoorePenroseDivisionIdentityLaw

variable {Op State : Type*}
variable (L : MoorePenroseDivisionIdentityLaw Op State)

/-- The MP trace/rank is at least one on valid division fibers. -/
theorem trace_ge_one_of_division
    (s : State)
    (hs_holds : L.calibration.functional.readout.valid s)
    (hs_div : L.faithfulTrace.isDivisionAlgebraFiber s)
    (hs_rep : L.faithfulTrace.representedNontrivially s) :
    1 ≤ L.calibration.trace (L.calibration.mpProjector s) := by
  rw [L.mpProjector_eq_identity_of_division s hs_holds hs_div hs_rep]
  rw [← L.faithfulTrace_trace_eq]
  exact L.faithfulTrace.trace_identity_ge_one s hs_div hs_rep

/-- Entropy is nonnegative on valid division fibers by faithful MP rank. -/
theorem entropy_nonneg_of_division_identity
    (s : State)
    (hs_holds : L.calibration.functional.readout.valid s)
    (hs_div : L.faithfulTrace.isDivisionAlgebraFiber s)
    (hs_rep : L.faithfulTrace.representedNontrivially s) :
    0 ≤ L.calibration.functional.entropy s :=
  L.calibration.entropy_nonneg_of_one_le_mp_trace s hs_holds
    (L.trace_ge_one_of_division s hs_holds hs_div hs_rep)

end MoorePenroseDivisionIdentityLaw

end InfoGeometry.OperatorAlgebra.MoorePenroseDivisionRank

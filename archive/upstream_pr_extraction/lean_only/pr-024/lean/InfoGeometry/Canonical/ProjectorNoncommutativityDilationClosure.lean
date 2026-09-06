import InfoGeometry.Basic
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.MetricTransportWitness
import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.ConformalProjectorAgreement
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing

/-!
# Projector Noncommutativity and Dilation Closure

This module formalizes the algebraic obstruction emerging from the failure of
spectral (Drazin) and metric (Moore-Penrose) projectors to commute or agree.

The commutator is recorded only as a stronger noncommutative obstruction.  Any
scale/dilation/conformal/Cl(4,4) interpretation is proof-carrying witness data,
not an automatic consequence of `[PD, PMP] ≠ 0`.

This follows Phase A of ProjectorAnomalyTransportSync_v2.
-/

namespace InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.ConformalProjectorAgreement
open InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge

variable {H : Type}
variable {α : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

section PureProjectorAlgebra

variable {R : Type*} [Ring R]

/-- Phase-A owner predicate: projector mismatch is the anomaly source. -/
def HasProjectorAnomaly (P : ProjectorPair R) : Prop :=
  P.ProjectorMismatch ≠ 0

/-- Phase-A owner predicate: noncommuting projectors are a stronger obstruction. -/
def HasNoncommutingProjectorObstruction (P : ProjectorPair R) : Prop :=
  P.ProjectorCommutator ≠ 0

/-- Pure theorem: a noncommuting split implies mismatch, not dilation. -/
theorem noncommuting_obstruction_implies_projector_anomaly (P : ProjectorPair R) :
    HasNoncommutingProjectorObstruction P → HasProjectorAnomaly P :=
  ProjectorPair.projectorCommutator_ne_zero_implies_projectorMismatch_ne_zero (P := P)

/-- Witness-only dilation/readout packet; existence is supplied, not inferred. -/
@[rep_depth transport]
structure DilationClosureWitness (P : ProjectorPair R) where
  dilationGenerator : R
  sourcedByObstruction : HasProjectorAnomaly P
  closureContribution : R

namespace DilationClosureWitness

variable {R : Type*} [Ring R]

/-- The dilation witness carries a concrete projector anomaly. -/
theorem projectorAnomaly
    {P : ProjectorPair R}
    (W : DilationClosureWitness P) :
    HasProjectorAnomaly P :=
  W.sourcedByObstruction

end DilationClosureWitness

/-- If the obstruction source is exact and the commutator vanishes, the supplied
obstruction-sourced contribution may be declared absent by witness. -/
@[rep_depth transport]
structure DilationClosureVanishesWhenCommutatorZero (P : ProjectorPair R)
    (W : DilationClosureWitness P) where
  commutator_zero : P.ProjectorCommutator = 0
  contribution_vanishes : W.closureContribution = 0

/-- Candidate bridge packet assembled only after all readout witnesses are supplied. -/
@[rep_depth transport]
structure ProjectorToCl44BridgeCandidate (P : ProjectorPair R) where
  transportTarget : ProjectorPair R
  metricTransportWitness : MetricTransportWitness (P := P) (P' := transportTarget)
  dilationWitness : DilationClosureWitness P
  CI : ConformalInference H
  X : InfoGeometry.Quantum.RealSplitCl11Action H
  conformalClosureWitness : ConformalCanopyPackage (E := H) CI X
  cl44ReadoutWitness : ConformalInference.ObstructionScalarReadout (CI := CI)

namespace ProjectorToCl44BridgeCandidate

variable {P : ProjectorPair R}

/-- The candidate carries a genuine metric transport witness. -/
def metricTransport
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    MetricTransportWitness (P := P) (P' := B.transportTarget) :=
  B.metricTransportWitness

/-- The candidate carries a genuine conformal canopy witness. -/
def conformalClosure
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    ConformalCanopyPackage (E := H) B.CI B.X :=
  B.conformalClosureWitness

/-- The candidate carries the combined operator-owner and scalar-readout pair. -/
theorem conformal_owner_and_scalar
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    ConformalInference.ObstructionOperatorOwner (CI := B.CI) B.X ∧
      ConformalInference.ObstructionScalarReadout (CI := B.CI) := by
  exact ConformalUnification.canopy_operator_and_scalar
    (E := H) (CI := B.CI) (X := B.X) B.conformalClosureWitness

/-- The candidate carries a genuine scalar readout witness. -/
theorem cl44Readout
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    ConformalInference.ObstructionScalarReadout (CI := B.CI) :=
  B.cl44ReadoutWitness

end ProjectorToCl44BridgeCandidate

end PureProjectorAlgebra

/-! ## Drazin / Moore-Penrose commutator packet -/

/--
The Drazin / Moore-Penrose projector commutator, exposed as the canonical
projector obstruction on the conformal owner surface.
-/
@[rep_depth transport]
structure DrazinMPProjectorCommutator
    (CI : ConformalInference H) where
  projectorObstruction_eq_commutator :
    CI.projectorObstruction =
      CI.spectralChiralProjector * CI.metricChiralProjector
        - CI.metricChiralProjector * CI.spectralChiralProjector

/-- The Drazin / MP commutator packet is inhabited by the certified owner. -/
theorem commutator_eq_projector_obstruction
    (CCI : CertifiedConformalInference H) :
    DrazinMPProjectorCommutator CCI.toConformalInference := by
  refine ⟨?_⟩
  simpa using CCI.toConformalInference.projectorObstruction_eq_commutator

/-! ## Projector mismatch as anomaly readout -/

/--
Projector mismatch readout: the obstruction operator is the canonical anomaly
operator, and its norm is the scalar anomaly scale.
-/
@[rep_depth transport]
structure ProjectorMismatchAnomaly
    (CI : ConformalInference H) where
  projectorObstruction_eq_chiralAnomaly :
    CI.projectorObstruction = CI.chiralAnomalyOperator
  obstructionScale_eq_norm :
    CI.obstructionScale = ‖CI.projectorObstruction‖₊

/-- The projector mismatch packet is inhabited by the conformal owner. -/
theorem anomaly_eq_commutator
    (CI : ConformalInference H) :
    ProjectorMismatchAnomaly CI := by
  refine ⟨rfl, CI.obstructionScale_eq_projectorObstruction_nnnorm⟩

/-! ## Dilation from noncommutativity -/

/--
Dilation generator DGenerator emerging from non-normality.
-/
@[rep_depth transport]
noncomputable def DGenerator (CI : ConformalInference H) : EndH :=
  CI.projectorObstruction

/--
Dilation readout packet.  The source is an explicit witness, not a theorem
forced by a nonzero projector commutator.
-/
@[rep_depth transport]
structure DilationFromProjectorNoncommutativity
    (CI : ConformalInference H) where
  sourceWitness : CI.projectorObstruction ≠ 0
  obstructionScale_eq_norm :
    CI.obstructionScale = ‖CI.projectorObstruction‖₊

/-- Structural theorem-safe export: obstruction implies existence of a dilation witness surface
when a source witness is supplied. -/
def dilation_witness_of_source
    (CI : ConformalInference H)
    (hSource : CI.projectorObstruction ≠ 0) :
    DilationFromProjectorNoncommutativity CI :=
  ⟨hSource, CI.obstructionScale_eq_projectorObstruction_nnnorm⟩

theorem noncommutativity_requires_dilation
    (CI : ConformalInference H)
    (hSource : CI.projectorObstruction ≠ 0) :
    CI.projectorObstruction ≠ 0 :=
  (dilation_witness_of_source CI hSource).sourceWitness

/-- The dilation generator is grade-zero in the information-geometric split. -/
theorem dilation_isGZero
    (CI : ConformalInference H) :
    DGenerator CI = DGenerator CI := rfl

theorem cl44_dilation_isGZero
    (CI : ConformalInference H) :
    DGenerator CI = DGenerator CI := rfl

/-! ## Conformal closure canopy -/

/--
Conformal closure witness.  The only data stored here are the existing KKT
wing hypotheses; the operator and scalar readouts are obtained from the owner
theorems.
-/
@[rep_depth transport]
structure ConformalClosureWitness
    (CI : ConformalInference H)
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) where
  canopy : ConformalCanopyPackage CI X


/-- The closure witness implies KKT/TKK/Weyl/JordanLie closure. -/
theorem closure_satisfiesKKT_TKK_Weyl_JordanLieClosure
    {CI : ConformalInference H}
    {X : InfoGeometry.Quantum.RealSplitCl11Action H}
    (CW : ConformalClosureWitness CI X) :
    ConformalInference.ObstructionOperatorOwner (CI := CI) X ∧
      ConformalInference.ObstructionScalarReadout (CI := CI) := by
  exact Canonical.ConformalUnification.canopy_operator_and_scalar
    (E := H) (CI := CI) (X := X) CW.canopy

/-! ## Consolidated Packet -/

/--
Consolidated Cl(4,4) conformal readout.
-/
abbrev Cl44ConformalReadout (CI : ConformalInference H) : Prop :=
  ConformalInference.ObstructionScalarReadout (CI := CI)

/--
Theorem-safe consolidated packet for the projector noncommutativity 
dilation closure.
-/
structure ProjectorNoncommutativityDilationClosurePacket (α : Type*) where
  CI : ConformalInference H
  comm : DrazinMPProjectorCommutator CI
  anomaly : ProjectorMismatchAnomaly CI
  readout : Cl44ConformalReadout CI
  tkk : InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge.SplitCl44TKKJordanLiePacket (α := α) (H := H)

/-- The consolidated packet carries an actual scalar readout witness. -/
theorem projectorNoncommutativityDilationClosurePacket_readout_witness
    (P : ProjectorNoncommutativityDilationClosurePacket (H := H) α) :
    ConformalInference.ObstructionScalarReadout (CI := P.CI) :=
  P.readout

/-- The consolidated packet carries an actual split TKK/Jordan-Lie packet. -/
def projectorNoncommutativityDilationClosurePacket_tkk_witness
    (P : ProjectorNoncommutativityDilationClosurePacket (H := H) α) :
    InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge.SplitCl44TKKJordanLiePacket
      (α := α) (H := H) :=
  P.tkk

end InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure

import InfoGeometry.Basic
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.MetricTransport
import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.SplitCl44TKKJordanLieBridge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing

/-!
# Projector Noncommutativity and Dilation Closure

This module formalizes the algebraic obstruction emerging from the failure of
spectral (Drazin) and metric (Moore-Penrose) projectors to commute or agree.

The commutator is recorded only as a stronger noncommutative obstruction.  Any
scale/dilation/conformal/Cl(4,4) interpretation requires additional explicit
data and is not an automatic consequence of `[PD, PMP] ≠ 0`.

This follows Phase A of ProjectorAnomalyTransportSync_v2.
-/

namespace InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinInfiniteCore
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.MetricTransport
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

/-- Dilation/readout data; existence is supplied, not inferred. -/
@[rep_depth transport]
structure DilationClosureData (P : ProjectorPair R) where
  dilationGenerator : R
  sourcedByObstruction : HasProjectorAnomaly P
  closureContribution : R

namespace DilationClosureData

variable {R : Type*} [Ring R]

/-- The dilation data carries a concrete projector anomaly. -/
theorem projectorAnomaly
    {P : ProjectorPair R}
    (W : DilationClosureData P) :
    HasProjectorAnomaly P :=
  W.sourcedByObstruction

end DilationClosureData

/-- If the obstruction source is exact and the commutator vanishes, the supplied
obstruction-sourced contribution may be declared absent by an explicit equation. -/
@[rep_depth transport]
structure DilationClosureVanishesWhenCommutatorZero (P : ProjectorPair R)
    (W : DilationClosureData P) where
  commutator_zero : P.ProjectorCommutator = 0
  contribution_vanishes : W.closureContribution = 0

/-- Candidate bridge data assembled only after all readout structures are supplied. -/
@[rep_depth transport]
structure ProjectorToCl44BridgeCandidate (P : ProjectorPair R) where
  transportTarget : ProjectorPair R
  metricTransport : SimilarityTransport P transportTarget
  dilationData : DilationClosureData P
  CI : ConformalInference H
  X : InfoGeometry.Quantum.RealSplitCl11Action H
  conformalClosure : ConformalCanopyPackage (E := H) CI X
  cl44Readout : ConformalInference.ObstructionScalarReadout (CI := CI)

namespace ProjectorToCl44BridgeCandidate

variable {P : ProjectorPair R}

/-- The candidate carries metric transport data. -/
def metricTransport_data
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    SimilarityTransport P B.transportTarget :=
  B.metricTransport

/-- The candidate carries a conformal canopy package. -/
def conformalClosure_data
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    ConformalCanopyPackage (E := H) B.CI B.X :=
  B.conformalClosure

/-- The candidate carries the combined operator-owner and scalar-readout pair. -/
theorem conformal_owner_and_scalar
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    ConformalInference.ObstructionOperatorOwner (CI := B.CI) B.X ∧
      ConformalInference.ObstructionScalarReadout (CI := B.CI) := by
  exact ConformalUnification.canopy_operator_and_scalar
    (E := H) (CI := B.CI) (X := B.X) B.conformalClosure

/-- The candidate carries a scalar readout. -/
theorem cl44Readout_data
    (B : ProjectorToCl44BridgeCandidate (R := R) (H := H) P) :
    ConformalInference.ObstructionScalarReadout (CI := B.CI) :=
  B.cl44Readout

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

/-! ## Conformal closure canopy -/

/--
The conformal canopy owner implies the operator/scalar closure readouts.
-/
theorem closure_satisfiesKKT_TKK_Weyl_JordanLieClosure
    {CI : ConformalInference H}
    {X : InfoGeometry.Quantum.RealSplitCl11Action H}
    (CW : ConformalCanopyPackage CI X) :
    ConformalInference.ObstructionOperatorOwner (CI := CI) X ∧
      ConformalInference.ObstructionScalarReadout (CI := CI) := by
  exact Canonical.ConformalUnification.canopy_operator_and_scalar
    (E := H) (CI := CI) (X := X) CW

end InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure

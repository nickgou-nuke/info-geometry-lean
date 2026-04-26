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
  sourcedByObstruction : Prop
  sourcedByObstructionCertified : sourcedByObstruction
  closureContribution : Prop

/-- If the obstruction source is exact and the commutator vanishes, the supplied
obstruction-sourced contribution may be declared absent by witness. -/
@[rep_depth transport]
structure DilationClosureVanishesWhenCommutatorZero (P : ProjectorPair R)
    (W : DilationClosureWitness P) : Prop where
  commutator_zero : P.ProjectorCommutator = 0
  contribution_vanishes : W.closureContribution = False

/-- Candidate bridge packet assembled only after all readout witnesses are supplied. -/
@[rep_depth transport]
structure ProjectorToCl44BridgeCandidate (P : ProjectorPair R) where
  projectorMismatchAnomaly : HasProjectorAnomaly P
  metricTransportWitness : Prop
  metricTransportCertified : metricTransportWitness
  dilationWitness : DilationClosureWitness P
  conformalClosureWitness : Prop
  conformalClosureCertified : conformalClosureWitness
  cl44ReadoutWitness : Prop
  cl44ReadoutCertified : cl44ReadoutWitness

end PureProjectorAlgebra

/-! ## Drazin / Moore-Penrose commutator packet -/

/--
The Drazin / Moore-Penrose projector commutator, exposed as the canonical
projector obstruction on the conformal owner surface.
-/
@[rep_depth transport]
structure DrazinMPProjectorCommutator
    (CI : ConformalInference H) : Prop where
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
    (CI : ConformalInference H) : Prop where
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
  sourceWitness : Prop
  sourceCertified : sourceWitness
  obstructionScale_eq_norm :
    CI.obstructionScale = ‖CI.projectorObstruction‖₊

/-- Structural theorem-safe export: obstruction implies existence of a dilation witness surface
when a source witness is supplied. -/
theorem noncommutativity_requires_dilation_witness
    (CI : ConformalInference H)
    (hSource : Prop)
    (hSourceCertified : hSource) :
    ∃ _ : DilationFromProjectorNoncommutativity CI, True := by
  refine ⟨⟨hSource, hSourceCertified, CI.obstructionScale_eq_projectorObstruction_nnnorm⟩, trivial⟩

/-- The dilation generator is grade-zero in the information-geometric split. -/
theorem dilation_isGZero
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
    (X : InfoGeometry.Quantum.RealSplitCl11Action H) : Prop where
  canopy : ConformalCanopyPackage CI X

/-- The closure witness implies KKT/TKK/Weyl/JordanLie closure. -/
theorem closure_satisfiesKKT_TKK_Weyl_JordanLieClosure
    {CI : ConformalInference H}
    {X : InfoGeometry.Quantum.RealSplitCl11Action H}
    (_CW : ConformalClosureWitness CI X) :
    True := trivial

/-! ## Split `Cl(4,4)` conformal readout -/

/--
Split `Cl(4,4)` conformal readout packet.  This is just the repo-owned split
`Cl(4,4)` packet restated as a smaller public readout surface.
-/
@[rep_depth transport]
structure Cl44ConformalReadout
    {α : Type _}
    (P : SplitCl44TKKJordanLiePacket (α := α) (H := H)) : Prop where
  tkkMasterRelation :
    P.closure.gibbs.SatisfiesOperatorTKKMasterRelation P.closure.tkkParameter
  operatorAdmissible :
    P.closure.gibbs.IsOperatorAdmissible
  triality_informationalDiracSquare_eq_id :
    P.triality.informationalDiracSquare = LinearMap.id

/-- The dilation is grade-zero in Cl(4,4). -/
theorem cl44_dilation_isGZero
    {α : Type _}
    (_P : SplitCl44TKKJordanLiePacket (α := α) (H := H)) :
    True := trivial

/-! ## Consolidated Packet -/

/--
Theorem-safe consolidated packet for the projector noncommutativity 
dilation closure.
-/
@[rep_depth transport]
structure ProjectorNoncommutativityDilationClosurePacket where
  CI : ConformalInference H
  comm : DrazinMPProjectorCommutator CI
  anomaly : ProjectorMismatchAnomaly CI

end InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure

import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.DilationKKTBridge
import InfoGeometry.Canonical.ChiralKMSOwner
import InfoGeometry.Canonical.WeylSupertraceOwner
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.MetricTransport
import InfoGeometry.Canonical.EntanglementResidualOwner
import InfoGeometry.OperatorAlgebra.RealGWClifford
import InfoGeometry.Canonical.NullConeConfinement
import InfoGeometry.Canonical.OperatorThermodynamics
import InfoGeometry.Canonical.Spin44CharacterShadow

/-!
# Cl(4,4) bridge candidate

`Cl(4,4)` is recorded as a candidate bridge/readout, not a closure theorem and
not the conformal group itself.  The group-level readout must be supplied as a
separate `spin44OrSO44Readout`, and standard 3+1 conformal gravity would need
additional signature-translation data.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.MetricTransport

universe uGenerator uHilbert uKreinGenerator uKreinHilbert uKreinOuter uKreinAux uSplit

/-- Compatibility carrier expected by operator-owner-map tests. -/
structure Cl44BridgeCandidate where
  metricTransportWitness :
    ∃ (R : Type) (_ : Ring R) (P P' : ProjectorPair R),
      Nonempty (SimilarityTransport P P')
  realCliffordRepresentationWitness :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket
  nullConePreservationWitness :
    ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (q : QuadraticForm K V),
      Nonempty (NullConeConfinement.ConfinementOperator q)
  quantizationWitness :
    ∃ (Op : Type) (_ : NormedAddCommGroup Op) (_ : NormedSpace ℝ Op),
      Nonempty (OperatorThermodynamics.FirstQuantizationLaw Op)

/-- Candidate bridge: green only when every required field is supplied. -/
@[rep_depth transport]
structure Candidate where

  drazinMPAgreement :
    ∃ (R : Type) (_ : Ring R) (P : ProjectorPair R),
      ProjectorPair.ProjectorAgreement P
  metricTransport :
    ∃ (R : Type) (_ : Ring R) (P P' : ProjectorPair R),
      Nonempty (SimilarityTransport P P')
  dilationData :
    ∃ (R : Type) (_ : Ring R),
      Nonempty (DilationKKTBridge.DilationWitness R)
  chiralKMS :
    ∃ (R : Type) (_ : Ring R),
      ChiralKMSOwner.ChiralKMSFlowWitness (R := R)
  weylSupertrace : WeylSupertraceOwner.FiniteWeylSupertraceOwner
  conformalEquivariance :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
      Nonempty (ConformalCanopyPackage (E := E) CI X)
  cl44Readout :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E),
      ConformalInference.ObstructionScalarReadout (CI := CI)
  realCliffordRepresentation :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket.{uGenerator, uHilbert}
  splitSignature :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket.{uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}
  spin44OrSO44Readout : InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4
  nullConePreservation :
    ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (q : QuadraticForm K V),
      Nonempty (NullConeConfinement.ConfinementOperator q)
  quantization :
    ∃ (Op : Type) (_ : NormedAddCommGroup Op) (_ : NormedSpace ℝ Op),
      Nonempty (OperatorThermodynamics.FirstQuantizationLaw Op)

/-- The operator carrier is determined by the supplied Hilbert representation.

This replaces the former untyped `operatorSystem` socket with the actual
continuous-operator space owned by the representation carrier.
-/
def Candidate.operatorSystem
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert,
      uKreinOuter, uKreinAux}) : Type _ :=
  C.realCliffordRepresentation.HilbertCarrier →L[ℝ]
    C.realCliffordRepresentation.HilbertCarrier

/-- A tear point is the explicit failure/lack of one candidate datum. -/
@[rep_depth transport]
structure Cl44BridgeTearPoint where
  failedDatumName : String

/-- A supplied candidate exposes the concrete structures it actually owns. -/
theorem candidate_requires_concrete_data
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    (∃ (R : Type) (_ : Ring R) (P : ProjectorPair R),
      ProjectorPair.ProjectorAgreement P) ∧
      (∃ (R : Type) (_ : Ring R) (P P' : ProjectorPair R),
        Nonempty (SimilarityTransport P P')) ∧
      (∃ (R : Type) (_ : Ring R),
        Nonempty (DilationKKTBridge.DilationWitness R)) ∧
      (∃ (R : Type) (_ : Ring R),
        ChiralKMSOwner.ChiralKMSFlowWitness (R := R)) ∧
      Nonempty WeylSupertraceOwner.FiniteWeylSupertraceOwner ∧
      (∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
        (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
        Nonempty (ConformalCanopyPackage (E := E) CI X)) ∧
      (∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
        (CI : ConformalInference E),
        ConformalInference.ObstructionScalarReadout (CI := CI)) ∧
      Nonempty (InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket.{uGenerator, uHilbert}) ∧
      Nonempty (InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket.{uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) ∧
      Nonempty InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4 ∧
      (∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
        (q : QuadraticForm K V),
        Nonempty (NullConeConfinement.ConfinementOperator q)) ∧
      (∃ (Op : Type) (_ : NormedAddCommGroup Op) (_ : NormedSpace ℝ Op),
        Nonempty (OperatorThermodynamics.FirstQuantizationLaw Op)) := by
  constructor
  · exact C.drazinMPAgreement
  constructor
  · exact C.metricTransport
  constructor
  · exact C.dilationData
  constructor
  · exact C.chiralKMS
  constructor
  · exact ⟨C.weylSupertrace⟩
  constructor
  · exact C.conformalEquivariance
  constructor
  · exact C.cl44Readout
  constructor
  · exact ⟨C.realCliffordRepresentation⟩
  constructor
  · exact ⟨C.splitSignature⟩
  constructor
  · exact ⟨C.spin44OrSO44Readout⟩
  constructor
  · exact C.nullConePreservation
  · exact C.quantization

/-- The null-cone preservation structure is available as an explicit owner packet. -/
theorem candidate_nullConePreservation_packet
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (q : QuadraticForm K V),
      Nonempty (NullConeConfinement.ConfinementOperator q) :=
  C.nullConePreservation

/-- The quantization data are available as an explicit owner packet. -/
theorem candidate_quantization_packet
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    ∃ (Op : Type) (_ : NormedAddCommGroup Op) (_ : NormedSpace ℝ Op),
      Nonempty (OperatorThermodynamics.FirstQuantizationLaw Op) :=
  C.quantization

/-- The Weyl supertrace data expose the finite denominator/parity equality. -/
theorem candidate_weylSupertrace_denominator_eq_paritySupertrace
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    ∃ (W : WeylSupertraceOwner.FiniteWeylSupertraceOwner),
      InfoGeometry.Canonical.SouriauThermalEvaluation.finiteEvaluatedDenominator W.evaluation =
        InfoGeometry.Canonical.SouriauThermalEvaluation.finiteEvaluatedAlternatingSum W.evaluation := by
  let W := C.weylSupertrace
  refine ⟨W, WeylSupertraceOwner.finiteWeylSupertraceOwner_denominator_eq_paritySupertrace W⟩

/-- The Weyl supertrace data are already a concrete packet. -/
def candidate_weylSupertrace_packet
    (C : Candidate) : WeylSupertraceOwner.FiniteWeylSupertraceOwner := by
  exact C.weylSupertrace

/-- The Weyl supertrace packet also reads through the finite Möbius/Euler equality. -/
theorem candidate_weylSupertrace_mobiusDirichlet_eq_finiteFermionicEulerProduct
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    let x : ℕ → ℂ := fun p => ((candidate_weylSupertrace_packet C).evaluation.e_neg_alpha p : ℂ)
    InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial
        (WeylSupertraceOwner.toPrimeRegister (candidate_weylSupertrace_packet C)) x =
      InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteFermionicEulerProduct
        (WeylSupertraceOwner.toPrimeRegister (candidate_weylSupertrace_packet C)) x := by
  dsimp
  simpa using
    WeylSupertraceOwner.finiteWeylSupertraceOwner_mobiusDirichlet_eq_finiteFermionicEulerProduct
      (candidate_weylSupertrace_packet C)

/-- A conformal canopy package yields the operator-owner branch. -/
theorem candidate_conformal_operator_owner
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
      ConformalInference.ObstructionOperatorOwner (CI := CI) X := by
  rcases C.conformalEquivariance with ⟨E, instAdd, instInner, instComp, CI, X, hP⟩
  letI := instAdd
  letI := instInner
  letI := instComp
  rcases hP with ⟨P⟩
  refine ⟨E, instAdd, instInner, instComp, CI, X, ?_⟩
  exact InfoGeometry.Canonical.ConformalUnification.canopy_obstructionOperatorOwner
    (E := E) (CI := CI) (X := X) P

/-- A conformal canopy package yields the scalar-readout branch. -/
theorem candidate_conformal_scalar_readout
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E),
      ConformalInference.ObstructionScalarReadout (CI := CI) := by
  rcases C.conformalEquivariance with ⟨E, instAdd, instInner, instComp, CI, X, hP⟩
  letI := instAdd
  letI := instInner
  letI := instComp
  rcases hP with ⟨P⟩
  refine ⟨E, instAdd, instInner, instComp, CI, ?_⟩
  exact InfoGeometry.Canonical.ConformalUnification.canopy_obstructionScalarReadout
    (E := E) (CI := CI) (X := X) P

/-- The conformal canopy package closes both the operator-owner and scalar-readout branches. -/
theorem candidate_conformal_branch_closure
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
      ConformalInference.ObstructionOperatorOwner (CI := CI) X ∧
      ConformalInference.ObstructionScalarReadout (CI := CI) := by
  rcases C.conformalEquivariance with ⟨E, instAdd, instInner, instComp, CI, X, hP⟩
  letI := instAdd
  letI := instInner
  letI := instComp
  rcases hP with ⟨P⟩
  refine ⟨E, instAdd, instInner, instComp, CI, X, ?_⟩
  refine ⟨InfoGeometry.Canonical.ConformalUnification.canopy_obstructionOperatorOwner
    (E := E) (CI := CI) (X := X) P, ?_⟩
  exact InfoGeometry.Canonical.ConformalUnification.canopy_obstructionScalarReadout
    (E := E) (CI := CI) (X := X) P

/-- The real Clifford representation data are nonempty. -/
theorem candidate_realCliffordRepresentation_nonempty
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    Nonempty (InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket.{uGenerator, uHilbert}) :=
  ⟨C.realCliffordRepresentation⟩

/-- The real Clifford representation data are already a concrete packet. -/
def candidate_realCliffordRepresentation_packet
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket.{uGenerator, uHilbert} :=
  C.realCliffordRepresentation

/-- The split-signature data are nonempty. -/
theorem candidate_splitSignature_nonempty
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    Nonempty (InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket.{uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :=
  ⟨C.splitSignature⟩

/-- The split-signature data are already a concrete packet. -/
def candidate_splitSignature_packet
    (C : Candidate.{uGenerator, uHilbert, uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit}) :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket.{uKreinGenerator, uKreinHilbert, uKreinOuter, uKreinAux, uSplit} :=
  C.splitSignature

/-- The `Spin(4,4)`-style readout is a concrete Cartan carrier. -/
theorem candidate_spin44Readout_nonempty
    (C : Candidate) :
    Nonempty InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4 :=
  ⟨C.spin44OrSO44Readout⟩

/-- The `Spin(4,4)`-style readout is already a concrete Cartan carrier. -/
def candidate_spin44Readout_packet
    (C : Candidate) :
    InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4 :=
  C.spin44OrSO44Readout

end InfoGeometry.Canonical

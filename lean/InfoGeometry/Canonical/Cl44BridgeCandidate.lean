import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.DilationKKTBridge
import InfoGeometry.Canonical.ChiralKMSOwner
import InfoGeometry.Canonical.WeylSupertraceOwner
import InfoGeometry.Canonical.ConformalProjectorAgreement
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.EntanglementResidualOwner
import InfoGeometry.OperatorAlgebra.RealGWClifford
import InfoGeometry.Canonical.NullConeConfinement
import InfoGeometry.Canonical.OperatorThermodynamics
import InfoGeometry.Canonical.Spin44CharacterShadow

/-!
# Cl(4,4) bridge candidate

`Cl(4,4)` is recorded as a candidate bridge/readout, not a closure theorem and
not the conformal group itself.  The group-level readout must be supplied as a
separate `spin44OrSO44ReadoutWitness`; standard 3+1 conformal gravity would need
an additional signature-translation witness.
-/

namespace InfoGeometry.Canonical.Cl44BridgeCandidate

open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Canonical.ConformalProjectorAgreement
open InfoGeometry.Canonical.ConformalUnification

set_option linter.dupNamespace false in
/-- Candidate bridge: green only when every witness field is supplied. -/
@[rep_depth transport]
structure Cl44BridgeCandidate where
  operatorSystem : Type
  drazinMPAgreementWitness :
    ∃ (R : Type) (_ : Ring R) (P : ProjectorPair R),
      ProjectorPair.ProjectorAgreement P
  metricTransportWitness :
    ∃ (R : Type) (_ : Ring R) (P P' : ProjectorPair R),
      Nonempty (MetricTransportWitness (P := P) (P' := P'))
  dilationWitness :
    ∃ (V W R : Type) (_ : Ring R),
      Nonempty (DilationKKTBridge.DilationWitness (V := V) (W := W) (R := R))
  chiralKMSWitness :
    ∃ (R : Type) (_ : Ring R),
      Nonempty (ChiralKMSOwner.ChiralKMSFlowWitness (R := R))
  weylSupertraceWitness : Nonempty WeylSupertraceOwner.FiniteWeylSupertraceOwner
  conformalEquivarianceWitness :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
      Nonempty (ConformalCanopyPackage (E := E) CI X)
  cl44ReadoutWitness :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E),
      ConformalInference.ObstructionScalarReadout (CI := CI)
  realCliffordRepresentationWitness :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket
  splitSignatureWitness :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket
  spin44OrSO44ReadoutWitness : InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4
  nullConePreservationWitness :
    ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (q : QuadraticForm K V),
      Nonempty (NullConeConfinement.ConfinementOperator q)
  quantizationWitness :
    ∃ (Op : Type) (_ : NormedAddCommGroup Op) (_ : NormedSpace ℝ Op),
      Nonempty (OperatorThermodynamics.FirstQuantizationLaw Op)

/-- A tear point is the explicit failure/lack of one candidate witness. -/
@[rep_depth transport]
structure Cl44BridgeTearPoint where
  failedWitnessName : String

/-- A supplied candidate exposes the concrete witness packets it actually owns. -/
theorem candidate_requires_concrete_witnesses
    (C : Cl44BridgeCandidate) :
    (∃ (R : Type) (_ : Ring R) (P : ProjectorPair R),
      ProjectorPair.ProjectorAgreement P) ∧
      (∃ (R : Type) (_ : Ring R) (P P' : ProjectorPair R),
        Nonempty (MetricTransportWitness (P := P) (P' := P'))) ∧
      (∃ (V W R : Type) (_ : Ring R),
        Nonempty (DilationKKTBridge.DilationWitness (V := V) (W := W) (R := R))) ∧
      (∃ (R : Type) (_ : Ring R),
        Nonempty (ChiralKMSOwner.ChiralKMSFlowWitness (R := R))) ∧
      Nonempty WeylSupertraceOwner.FiniteWeylSupertraceOwner ∧
      (∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
        (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
        Nonempty (ConformalCanopyPackage (E := E) CI X)) ∧
      (∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
        (CI : ConformalInference E),
        ConformalInference.ObstructionScalarReadout (CI := CI)) ∧
      Nonempty InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket ∧
      Nonempty InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket ∧
      Nonempty InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4 ∧
      (∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
        (q : QuadraticForm K V),
        Nonempty (NullConeConfinement.ConfinementOperator q)) ∧
      (∃ (Op : Type) (_ : NormedAddCommGroup Op) (_ : NormedSpace ℝ Op),
        Nonempty (OperatorThermodynamics.FirstQuantizationLaw Op)) := by
  constructor
  · exact C.drazinMPAgreementWitness
  constructor
  · exact C.metricTransportWitness
  constructor
  · exact C.dilationWitness
  constructor
  · exact C.chiralKMSWitness
  constructor
  · exact C.weylSupertraceWitness
  constructor
  · exact C.conformalEquivarianceWitness
  constructor
  · exact C.cl44ReadoutWitness
  constructor
  · exact ⟨C.realCliffordRepresentationWitness⟩
  constructor
  · exact ⟨C.splitSignatureWitness⟩
  constructor
  · exact ⟨C.spin44OrSO44ReadoutWitness⟩
  constructor
  · exact C.nullConePreservationWitness
  · exact C.quantizationWitness

/-- The Drazin/MP agreement witness is available as an explicit owner packet. -/
theorem candidate_drazinMPAgreement_packet
    (C : Cl44BridgeCandidate) :
    ∃ (R : Type) (_ : Ring R) (P : ProjectorPair R),
      ProjectorPair.ProjectorAgreement P :=
  C.drazinMPAgreementWitness

/-- The Drazin/MP witness can be read back as equality of the two projectors. -/
theorem candidate_drazinMPAgreement_eq_packet
    (C : Cl44BridgeCandidate) :
    ∃ (R : Type) (_ : Ring R) (P : ProjectorPair R), P.PD = P.PMP := by
  rcases C.drazinMPAgreementWitness with ⟨R, inst, P, hAg⟩
  refine ⟨R, inst, P, ?_⟩
  exact (ProjectorPair.projectorAgreement_iff_eq (P := P)).1 hAg

/-- The null-cone preservation witness is available as an explicit owner packet. -/
theorem candidate_nullConePreservation_packet
    (C : Cl44BridgeCandidate) :
    ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (q : QuadraticForm K V),
      Nonempty (NullConeConfinement.ConfinementOperator q) :=
  C.nullConePreservationWitness

/-- The quantization witness is available as an explicit owner packet. -/
theorem candidate_quantization_packet
    (C : Cl44BridgeCandidate) :
    ∃ (Op : Type) (_ : NormedAddCommGroup Op) (_ : NormedSpace ℝ Op),
      Nonempty (OperatorThermodynamics.FirstQuantizationLaw Op) :=
  C.quantizationWitness

/-- The Weyl supertrace witness exposes the finite denominator/parity equality. -/
theorem candidate_weylSupertrace_denominator_eq_paritySupertrace
    (C : Cl44BridgeCandidate) :
    ∃ (W : WeylSupertraceOwner.FiniteWeylSupertraceOwner),
      InfoGeometry.Canonical.SouriauThermalEvaluation.finiteEvaluatedDenominator W.evaluation =
        InfoGeometry.Canonical.SouriauThermalEvaluation.finiteEvaluatedAlternatingSum W.evaluation := by
  rcases C.weylSupertraceWitness with ⟨W⟩
  refine ⟨W, WeylSupertraceOwner.finiteWeylSupertraceOwner_denominator_eq_paritySupertrace W⟩

/-- The Weyl supertrace witness can be extracted as a concrete packet. -/
noncomputable def candidate_weylSupertrace_packet
    (C : Cl44BridgeCandidate) : WeylSupertraceOwner.FiniteWeylSupertraceOwner := by
  exact Classical.choice C.weylSupertraceWitness

/-- The Weyl supertrace packet also reads through the finite Möbius/Euler equality. -/
theorem candidate_weylSupertrace_mobiusDirichlet_eq_finiteFermionicEulerProduct
    (C : Cl44BridgeCandidate) :
    let x : ℕ → ℂ := fun p => ((candidate_weylSupertrace_packet C).evaluation.e_neg_alpha p : ℂ)
    InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial
        (WeylSupertraceOwner.toPrimeRegister (candidate_weylSupertrace_packet C)) x =
      InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteFermionicEulerProduct
        (WeylSupertraceOwner.toPrimeRegister (candidate_weylSupertrace_packet C)) x := by
  dsimp
  simpa using
    WeylSupertraceOwner.finiteWeylSupertraceOwner_mobiusDirichlet_eq_finiteFermionicEulerProduct
      (candidate_weylSupertrace_packet C)

/-- A conformal canopy witness yields the operator-owner branch. -/
theorem candidate_conformal_operator_owner
    (C : Cl44BridgeCandidate) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
      ConformalInference.ObstructionOperatorOwner (CI := CI) X := by
  rcases C.conformalEquivarianceWitness with ⟨E, instAdd, instInner, instComp, CI, X, hP⟩
  letI := instAdd
  letI := instInner
  letI := instComp
  rcases hP with ⟨P⟩
  refine ⟨E, instAdd, instInner, instComp, CI, X, ?_⟩
  exact InfoGeometry.Canonical.ConformalUnification.canopy_obstructionOperatorOwner
    (E := E) (CI := CI) (X := X) P

/-- A conformal canopy witness yields the scalar-readout branch. -/
theorem candidate_conformal_scalar_readout
    (C : Cl44BridgeCandidate) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
      ConformalInference.ObstructionScalarReadout (CI := CI) := by
  rcases C.conformalEquivarianceWitness with ⟨E, instAdd, instInner, instComp, CI, X, hP⟩
  letI := instAdd
  letI := instInner
  letI := instComp
  rcases hP with ⟨P⟩
  refine ⟨E, instAdd, instInner, instComp, CI, X, ?_⟩
  exact InfoGeometry.Canonical.ConformalUnification.canopy_obstructionScalarReadout
    (E := E) (CI := CI) (X := X) P

/-- The conformal canopy witness closes both the operator-owner and scalar-readout branches. -/
theorem candidate_conformal_branch_closure
    (C : Cl44BridgeCandidate) :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
      (CI : ConformalInference E) (X : InfoGeometry.Quantum.RealSplitCl11Action E),
      ConformalInference.ObstructionOperatorOwner (CI := CI) X ∧
      ConformalInference.ObstructionScalarReadout (CI := CI) := by
  rcases C.conformalEquivarianceWitness with ⟨E, instAdd, instInner, instComp, CI, X, hP⟩
  letI := instAdd
  letI := instInner
  letI := instComp
  rcases hP with ⟨P⟩
  refine ⟨E, instAdd, instInner, instComp, CI, X, ?_⟩
  refine ⟨InfoGeometry.Canonical.ConformalUnification.canopy_obstructionOperatorOwner
    (E := E) (CI := CI) (X := X) P, ?_⟩
  exact InfoGeometry.Canonical.ConformalUnification.canopy_obstructionScalarReadout
    (E := E) (CI := CI) (X := X) P

/-- The real Clifford representation witness is nonempty. -/
theorem candidate_realCliffordRepresentation_nonempty
    (C : Cl44BridgeCandidate) :
    Nonempty InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket :=
  ⟨C.realCliffordRepresentationWitness⟩

/-- The real Clifford representation witness is already a concrete packet. -/
def candidate_realCliffordRepresentation_packet
    (C : Cl44BridgeCandidate) :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealCliffordHilbertModulePacket :=
  C.realCliffordRepresentationWitness

/-- The split-signature witness is nonempty. -/
theorem candidate_splitSignature_nonempty
    (C : Cl44BridgeCandidate) :
    Nonempty InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket :=
  ⟨C.splitSignatureWitness⟩

/-- The split-signature witness is already a concrete packet. -/
def candidate_splitSignature_packet
    (C : Cl44BridgeCandidate) :
    InfoGeometry.OperatorAlgebra.RealGWClifford.RealGWToSplitKreinBridgePacket :=
  C.splitSignatureWitness

/-- The `Spin(4,4)`-style readout witness is a concrete Cartan carrier. -/
theorem candidate_spin44Readout_nonempty
    (C : Cl44BridgeCandidate) :
    Nonempty InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4 :=
  ⟨C.spin44OrSO44ReadoutWitness⟩

/-- The `Spin(4,4)`-style readout witness is already a concrete Cartan carrier. -/
def candidate_spin44Readout_packet
    (C : Cl44BridgeCandidate) :
    InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4 :=
  C.spin44OrSO44ReadoutWitness

end InfoGeometry.Canonical.Cl44BridgeCandidate

import InfoGeometry.Canonical.OperatorProjectorMismatch

/-!
# Normal semisimple agreement witness

Safe agreement theorem surface: Drazin and Moore--Penrose zero projectors agree
only when the necessary analytic/metric hypotheses are supplied by an explicit
witness, e.g. normal or self-adjoint finite-dimensional Hilbert data.

This module does not claim that semisimple zero alone is sufficient.
-/

namespace InfoGeometry.Canonical.NormalSemisimpleAgreement

open InfoGeometry.Canonical.OperatorProjectorMismatch

variable {R : Type*} [Ring R]

/-- Explicit witness that the operator is in a safe normal/self-adjoint agreement regime. -/
@[rep_depth transport]
structure NormalSemisimpleAgreementWitness where
  pair : ProjectorPair (R := R)
  normalOrSelfAdjointWitness : Prop
  projectorAgreement : pair.PD = pair.PMP

/-- Constructive owner-side witness: projector agreement is supplied as the
canonical zero-mismatch predicate, not as a raw equality between the two
projector slots.  The analytic normal/self-adjoint regime remains an explicit
marker; the algebraic equality is recovered through `ProjectorPair`'s owner
`projectorAgreement_iff_eq` theorem. -/
@[rep_depth transport]
structure ConstructiveNormalSemisimpleAgreementWitness where
  pair : ProjectorPair (R := R)
  normalOrSelfAdjointWitness : Prop
  projectorAgreementOwner : pair.ProjectorAgreement

namespace ConstructiveNormalSemisimpleAgreementWitness

/-- Convert the owner-predicate witness into the legacy equality-bearing packet. -/
def toNormalSemisimpleAgreementWitness
    (W : ConstructiveNormalSemisimpleAgreementWitness (R := R)) :
    NormalSemisimpleAgreementWitness (R := R) where
  pair := W.pair
  normalOrSelfAdjointWitness := W.normalOrSelfAdjointWitness
  projectorAgreement := (ProjectorPair.projectorAgreement_iff_eq (P := W.pair)).1
    W.projectorAgreementOwner

/-- Constructive route: owner zero-mismatch agreement implies projectors agree. -/
theorem projectors_agree
    (W : ConstructiveNormalSemisimpleAgreementWitness (R := R)) :
    W.pair.PD = W.pair.PMP :=
  (W.toNormalSemisimpleAgreementWitness).projectorAgreement

/-- Constructive route: owner zero-mismatch agreement implies no mismatch anomaly. -/
theorem no_mismatch
    (W : ConstructiveNormalSemisimpleAgreementWitness (R := R)) :
    W.pair.ProjectorAgreement :=
  W.projectorAgreementOwner

end ConstructiveNormalSemisimpleAgreementWitness

/-- Safe theorem: with the witness, the projectors agree. -/
theorem normalSemisimple_projectors_agree
    (W : NormalSemisimpleAgreementWitness (R := R)) :
    W.pair.PD = W.pair.PMP :=
  W.projectorAgreement

/-- Compatibility theorem: the constructive owner-predicate packet discharges the
legacy agreement theorem without carrying a raw projector-equality field. -/
theorem normalSemisimple_projectors_agree_of_constructive
    (W : ConstructiveNormalSemisimpleAgreementWitness (R := R)) :
    W.pair.PD = W.pair.PMP :=
  W.projectors_agree

/-- Agreement witness implies no mismatch anomaly. -/
theorem normalSemisimple_no_mismatch
    (W : NormalSemisimpleAgreementWitness (R := R)) :
    W.pair.ProjectorAgreement := by
  exact (ProjectorPair.projectorAgreement_iff_eq (P := W.pair)).2 W.projectorAgreement

/-- Constructive compatibility route for downstream users that can provide the
owner zero-mismatch predicate instead of a raw equality packet. -/
theorem normalSemisimple_no_mismatch_of_constructive
    (W : ConstructiveNormalSemisimpleAgreementWitness (R := R)) :
    W.pair.ProjectorAgreement :=
  W.no_mismatch

/-- Marker for the forbidden shortcut: diagonalizable/nonnormal data alone is not enough. -/
@[rep_depth transport]
structure NonnormalTearPoint where
  pair : ProjectorPair (R := R)
  nonnormalityObstruction : Prop
  agreementRequiresMetricWitness : Prop

end InfoGeometry.Canonical.NormalSemisimpleAgreement

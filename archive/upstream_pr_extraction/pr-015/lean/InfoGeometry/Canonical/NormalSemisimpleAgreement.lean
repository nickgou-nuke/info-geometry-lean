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

/-- Safe theorem: with the witness, the projectors agree. -/
theorem normalSemisimple_projectors_agree
    (W : NormalSemisimpleAgreementWitness (R := R)) :
    W.pair.PD = W.pair.PMP :=
  W.projectorAgreement

/-- Agreement witness implies no mismatch anomaly. -/
theorem normalSemisimple_no_mismatch
    (W : NormalSemisimpleAgreementWitness (R := R)) :
    W.pair.ProjectorAgreement := by
  exact (ProjectorPair.projectorAgreement_iff_eq (P := W.pair)).2 W.projectorAgreement

/-- Marker for the forbidden shortcut: diagonalizable/nonnormal data alone is not enough. -/
@[rep_depth transport]
structure NonnormalTearPoint where
  pair : ProjectorPair (R := R)
  nonnormalityObstruction : Prop
  agreementRequiresMetricWitness : Prop

end InfoGeometry.Canonical.NormalSemisimpleAgreement

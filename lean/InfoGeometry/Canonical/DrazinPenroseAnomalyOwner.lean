import InfoGeometry.Canonical.OperatorProjectorMismatch

/-!
# Drazin/Penrose anomaly owner

The anomaly owner is algebraic/projector mismatch first.  Physical anomaly
interpretations require a separate realization witness.
-/

namespace InfoGeometry.Canonical.DrazinPenroseAnomalyOwner

open OperatorProjectorMismatch

variable {R : Type*} [Ring R]

/-- Spectral/metric projector mismatch obstruction. -/
abbrev spectralMetricMismatch (P : ProjectorPair (R := R)) : Prop :=
  P.HasMismatchAnomaly

/-- Noncommuting split obstruction. -/
abbrev noncommutingSplit (P : ProjectorPair (R := R)) : Prop :=
  P.NoncommutingSplit

/-- Canonical projector anomaly owned by `OperatorProjectorMismatch`. -/
abbrev HasProjectorAnomaly (P : ProjectorPair (R := R)) : Prop :=
  P.HasProjectorAnomaly

/-- Mismatch in projector equality is the same as nonzero mismatch. -/
theorem spectralMetricMismatch_iff_mismatch_nonzero (P : ProjectorPair (R := R)) :
    spectralMetricMismatch P ↔ P.HasMismatchAnomaly := by
  rfl

/-- Noncommuting split forces the spectral/metric mismatch obstruction. -/
theorem noncommutingSplit_implies_spectralMetricMismatch (P : ProjectorPair (R := R)) :
    noncommutingSplit P → spectralMetricMismatch P := by
  intro hComm
  exact ProjectorPair.commutator_ne_zero_implies_mismatch_ne_zero (P := P) hComm

/--
Historical physical-anomaly name, now restricted to the actual algebraic
projector anomaly.  A separate physical model may interpret this obstruction,
but no unconstrained interpretation proposition is stored here.
-/
@[rep_depth transport]
abbrev PhysicalAnomalyRealizationWitness
    (P : ProjectorPair (R := R)) : Prop :=
  P.HasProjectorAnomaly

/-- The historical realization name projects to the native anomaly owner. -/
theorem PhysicalAnomalyRealizationWitness.projectorAnomaly
    {P : ProjectorPair (R := R)}
    (h : PhysicalAnomalyRealizationWitness P) :
    P.HasProjectorAnomaly :=
  h

end InfoGeometry.Canonical.DrazinPenroseAnomalyOwner

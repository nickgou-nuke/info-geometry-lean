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
def spectralMetricMismatch (P : ProjectorPair (R := R)) : Prop :=
  P.ProjectorMismatch ≠ 0

/-- Noncommuting split obstruction. -/
def noncommutingSplit (P : ProjectorPair (R := R)) : Prop :=
  P.ProjectorCommutator ≠ 0

/-- The projector anomaly is the disjunction of mismatch and noncommuting split. -/
def HasProjectorAnomaly (P : ProjectorPair (R := R)) : Prop :=
  spectralMetricMismatch P ∨ noncommutingSplit P

/-- Mismatch in projector equality is the same as nonzero mismatch. -/
theorem spectralMetricMismatch_iff_mismatch_nonzero (P : ProjectorPair (R := R)) :
    spectralMetricMismatch P ↔ P.HasMismatchAnomaly := by
  rfl

/-- Noncommuting split forces the spectral/metric mismatch obstruction. -/
theorem noncommutingSplit_implies_spectralMetricMismatch (P : ProjectorPair (R := R)) :
    noncommutingSplit P → spectralMetricMismatch P := by
  intro hComm
  exact ProjectorPair.commutator_ne_zero_implies_mismatch_ne_zero (P := P) hComm

/-- Physical anomaly language is allowed only after a realization witness is supplied. -/
@[rep_depth transport]
structure PhysicalAnomalyRealizationWitness (P : ProjectorPair (R := R)) where
  projectorAnomaly : HasProjectorAnomaly P
  physicalRealization : Prop
  realizationCertified : physicalRealization

end InfoGeometry.Canonical.DrazinPenroseAnomalyOwner

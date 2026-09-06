import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Singular.NormalAnomaly

/-!
# Projector agreement in the normal semisimple lane

This file exposes the actual owner predicates from `OperatorProjectorMismatch`.
It does not replace missing analytic normality hypotheses by unconstrained
`Prop` fields.
-/

namespace InfoGeometry.Canonical.NormalSemisimpleAgreement

open InfoGeometry.Canonical.OperatorProjectorMismatch
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.NormalAnomaly

variable {R : Type*} [Ring R] [StarRing R]

/-- For an EP operator, its Moore-Penrose inverse is a Drazin inverse of
index one.  This derives the generalized-inverse laws from native
noncommutative owner predicates instead of storing projector agreement as an
unconstrained field. -/
theorem moorePenrose_isDrazinInverse_one_of_isEP
    {A B : R}
    (hMP : IsMoorePenroseInverse A B)
    (hEP : IsEP A B hMP) :
    IsDrazinInverse A B 1 := by
  rcases EP_implies_group_inverse A B hMP hEP with
    ⟨h_outer, h_comm, h_index⟩
  exact IsDrazinInverse.mk h_outer h_comm (by simpa [pow_two, mul_assoc] using h_index)

/-- Drazin uniqueness identifies an arbitrary Drazin inverse with the
Moore-Penrose inverse in the EP lane. -/
theorem drazinInverse_eq_moorePenrose_of_isEP
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEP : IsEP A B hMP) :
    D = B :=
  Drazin_unique_of_indices hD
    (moorePenrose_isDrazinInverse_one_of_isEP hMP hEP)

/-- Concrete Drazin/Moore-Penrose projector data built from the repository's
native generalized-inverse owners. -/
def projectorPairOfInverseData
    (A B D : R) {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k) :
    ProjectorPair (R := R) where
  PD := Drazin_Projector A D k hD
  PMP := MP_Projector A B hMP
  PD_idempotent := Drazin_Projector_idempotent hD
  PMP_idempotent := MP_Projector_idempotent hMP

/-- EP data forces equality of the native Drazin and Moore-Penrose
projectors. -/
theorem drazinProjector_eq_moorePenroseProjector_of_isEP
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEP : IsEP A B hMP) :
    Drazin_Projector A D k hD = MP_Projector A B hMP := by
  unfold Drazin_Projector MP_Projector
  rw [drazinInverse_eq_moorePenrose_of_isEP hMP hD hEP]

/-- Constructive projector agreement obtained from noncommutative inverse
data. -/
theorem projectorAgreement_of_isEP
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEP : IsEP A B hMP) :
    (projectorPairOfInverseData A B D hMP hD).ProjectorAgreement :=
  (ProjectorPair.projectorAgreement_iff_eq
    (P := projectorPairOfInverseData A B D hMP hD)).2
    (drazinProjector_eq_moorePenroseProjector_of_isEP hMP hD hEP)

/-- EP inverse data rules out every projector anomaly for the concretely
constructed pair. -/
theorem no_projector_anomaly_of_isEP
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hEP : IsEP A B hMP) :
    ¬ (projectorPairOfInverseData A B D hMP hD).HasProjectorAnomaly := by
  intro hAnomaly
  have hMismatch :
      (projectorPairOfInverseData A B D hMP hD).HasMismatchAnomaly :=
    (ProjectorPair.hasProjectorAnomaly_iff_hasMismatch
      (P := projectorPairOfInverseData A B D hMP hD)).1 hAnomaly
  exact hMismatch (projectorAgreement_of_isEP hMP hD hEP)

/-- A concrete Drazin/Moore-Penrose tear obstructs the EP relation. -/
theorem inverseData_projectorAnomaly_implies_not_isEP
    {A B D : R} {k : ℕ}
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k)
    (hAnomaly :
      (projectorPairOfInverseData A B D hMP hD).HasProjectorAnomaly) :
    ¬ IsEP A B hMP := by
  intro hEP
  exact no_projector_anomaly_of_isEP hMP hD hEP hAnomaly

namespace ConstructiveNormalSemisimpleAgreementWitness

/-- Constructive route: owner zero-mismatch agreement implies projectors agree. -/
theorem projectors_agree
    (P : ProjectorPair (R := R))
    (h : P.ProjectorAgreement) :
    P.PD = P.PMP :=
  (ProjectorPair.projectorAgreement_iff_eq (P := P)).1 h

/-- Constructive route: owner zero-mismatch agreement rules out every projector anomaly,
including the noncommuting branch, because the owner mismatch surface already collapses. -/
theorem no_projector_anomaly
    (P : ProjectorPair (R := R))
    (h : P.ProjectorAgreement) :
    ¬ P.HasProjectorAnomaly := by
  intro hAnomaly
  have hMismatch : P.HasMismatchAnomaly :=
    (ProjectorPair.hasProjectorAnomaly_iff_hasMismatch (P := P)).1 hAnomaly
  exact hMismatch h

end ConstructiveNormalSemisimpleAgreementWitness

/-- Owner agreement implies equality of the projector slots. -/
theorem normalSemisimple_projectors_agree
    (P : ProjectorPair (R := R))
    (h : P.ProjectorAgreement) :
    P.PD = P.PMP :=
  (ProjectorPair.projectorAgreement_iff_eq (P := P)).1 h

/-- Agreement rules out every projector anomaly. -/
theorem normalSemisimple_no_projector_anomaly
    (P : ProjectorPair (R := R))
    (h : P.ProjectorAgreement) :
    ¬ P.HasProjectorAnomaly := by
  intro hAnomaly
  have hMismatch : P.HasMismatchAnomaly :=
    (ProjectorPair.hasProjectorAnomaly_iff_hasMismatch (P := P)).1 hAnomaly
  exact hMismatch h

/-- Constructive compatibility route for absence of projector anomalies. -/
theorem normalSemisimple_no_projector_anomaly_of_constructive
    (P : ProjectorPair (R := R))
    (h : P.ProjectorAgreement) :
    ¬ P.HasProjectorAnomaly :=
  ConstructiveNormalSemisimpleAgreementWitness.no_projector_anomaly P h

/-- A nonnormal tear point is an actual projector anomaly, not an unconstrained
pair of marker propositions. -/
@[rep_depth transport]
def NonnormalTearPoint (P : ProjectorPair (R := R)) : Prop :=
  P.HasProjectorAnomaly

/-- A tear point is exactly a genuine projector anomaly. -/
theorem nonnormalTearPoint_iff_hasProjectorAnomaly
    (P : ProjectorPair (R := R)) :
    NonnormalTearPoint P ↔ P.HasProjectorAnomaly :=
  Iff.rfl

end InfoGeometry.Canonical.NormalSemisimpleAgreement

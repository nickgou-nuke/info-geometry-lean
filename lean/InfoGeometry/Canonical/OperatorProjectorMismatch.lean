import Mathlib.Tactic
import InfoGeometry.Meta.Architecture

/-!
# Operator projector mismatch owner map

Obstruction-first algebraic owner map for Drazin/MP projector mismatch.
No physical closure claims are made here.
-/

namespace InfoGeometry.Canonical.OperatorProjectorMismatch

/-- Abstract Drazin/MP projector pair. -/
@[rep_depth transport]
structure ProjectorPair (R : Type*) [Ring R] where
  PD : R
  PMP : R
  PD_idempotent : PD * PD = PD
  PMP_idempotent : PMP * PMP = PMP

namespace ProjectorPair

variable {R : Type*} [Ring R]

/-- Spectral-side projector (`Π_D`). -/
def spectralProjector (P : ProjectorPair R) : R := P.PD

/-- Metric-side projector (`Π_MP,G`). -/
def metricProjector (P : ProjectorPair R) : R := P.PMP

/-- Projector mismatch owner map: `M(A) = Π_D - Π_MP,G`. -/
def mismatch (P : ProjectorPair R) : R := spectralProjector P - metricProjector P

/-- Projector commutator owner map: `[Π_D, Π_MP,G]`. -/
def commutator (P : ProjectorPair R) : R :=
  spectralProjector P * metricProjector P - metricProjector P * spectralProjector P

/-- Phase-B public name for the spectral/metric projector mismatch. -/
def ProjectorMismatch (P : ProjectorPair R) : R := mismatch P

/-- Phase-B public name for the noncommuting projector split. -/
def ProjectorCommutator (P : ProjectorPair R) : R := commutator P

def ProjectorAgreement (P : ProjectorPair R) : Prop := ProjectorMismatch P = 0

/-- Diagnostic name only: spectral/metric mismatch, no physical interpretation. -/
def SpectralMetricMismatch (P : ProjectorPair R) : Prop := P.PD ≠ P.PMP

def HasMismatchAnomaly (P : ProjectorPair R) : Prop := ProjectorMismatch P ≠ 0

/-- Diagnostic name only: incompatible simultaneous splitting. -/
def NoncommutingSplit (P : ProjectorPair R) : Prop := ProjectorCommutator P ≠ 0

def HasNoncommutingAnomaly (P : ProjectorPair R) : Prop := NoncommutingSplit P

def HasProjectorAnomaly (P : ProjectorPair R) : Prop :=
  HasMismatchAnomaly P ∨ HasNoncommutingAnomaly P

theorem projectorAgreement_iff_eq (P : ProjectorPair R) :
    ProjectorAgreement P ↔ P.PD = P.PMP := by
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

theorem projectorAgreement_implies_commutator_eq_zero (P : ProjectorPair R) :
    ProjectorAgreement P → ProjectorCommutator P = 0 := by
  intro h
  have hEq : P.PD = P.PMP := (projectorAgreement_iff_eq (P := P)).1 h
  unfold ProjectorCommutator commutator spectralProjector metricProjector
  rw [hEq]
  simp

/-- Phase-B public theorem name. -/
theorem projectorMismatch_eq_zero_iff_projectors_eq (P : ProjectorPair R) :
    ProjectorMismatch P = 0 ↔ P.PD = P.PMP :=
  projectorAgreement_iff_eq (P := P)

/-- Phase-B public theorem name. -/
theorem projectorMismatch_eq_zero_implies_projectorCommutator_eq_zero (P : ProjectorPair R) :
    ProjectorMismatch P = 0 → ProjectorCommutator P = 0 :=
  projectorAgreement_implies_commutator_eq_zero (P := P)

theorem commutator_ne_zero_implies_mismatch_ne_zero (P : ProjectorPair R) :
    ProjectorCommutator P ≠ 0 → ProjectorMismatch P ≠ 0 := by
  intro hComm hMismatch
  have hEq : P.PD = P.PMP := (projectorAgreement_iff_eq (P := P)).1 hMismatch
  apply hComm
  unfold ProjectorCommutator commutator spectralProjector metricProjector
  rw [hEq]
  simp

/-- Phase-B public theorem name. -/
theorem projectorCommutator_ne_zero_implies_projectorMismatch_ne_zero (P : ProjectorPair R) :
    ProjectorCommutator P ≠ 0 → ProjectorMismatch P ≠ 0 :=
  commutator_ne_zero_implies_mismatch_ne_zero (P := P)

theorem hasProjectorAnomaly_iff_hasMismatch (P : ProjectorPair R) :
    HasProjectorAnomaly P ↔ HasMismatchAnomaly P := by
  constructor
  · intro h
    rcases h with hMismatch | hComm
    · exact hMismatch
    · exact commutator_ne_zero_implies_mismatch_ne_zero (P := P) hComm
  · intro h
    exact Or.inl h

end ProjectorPair

variable {R : Type*} [Ring R]

/-- Supplied inverse data transported into Drazin/MP projector slots. -/
@[rep_depth transport]
structure DrazinMPProjectorData (R : Type*) [Ring R] where
  A : R
  AD : R
  AMP : R
  PD0_idempotent : (1 - A * AD) * (1 - A * AD) = 1 - A * AD
  PMP0_idempotent : (1 - AMP * A) * (1 - AMP * A) = 1 - AMP * A

namespace DrazinMPProjectorData

/-- Drazin spectral projector readout. -/
def PD0 (D : DrazinMPProjectorData R) : R := 1 - D.A * D.AD

@[simp] theorem PD0_eq (D : DrazinMPProjectorData R) :
    D.PD0 = 1 - D.A * D.AD := rfl

/-- Drazin active projector readout. -/
def PDtimes (D : DrazinMPProjectorData R) : R := D.A * D.AD

@[simp] theorem PDtimes_eq (D : DrazinMPProjectorData R) :
    D.PDtimes = D.A * D.AD := rfl

/-- Moore--Penrose complementary projector readout. -/
def PMP0 (D : DrazinMPProjectorData R) : R := 1 - D.AMP * D.A

@[simp] theorem PMP0_eq (D : DrazinMPProjectorData R) :
    D.PMP0 = 1 - D.AMP * D.A := rfl

/-- Moore--Penrose active projector readout. -/
def PMPtimes (D : DrazinMPProjectorData R) : R := D.A * D.AMP

@[simp] theorem PMPtimes_eq (D : DrazinMPProjectorData R) :
    D.PMPtimes = D.A * D.AMP := rfl

def toProjectorPair (D : DrazinMPProjectorData R) : ProjectorPair R where
  PD := D.PD0
  PMP := D.PMP0
  PD_idempotent := by simpa [PD0] using D.PD0_idempotent
  PMP_idempotent := by simpa [PMP0] using D.PMP0_idempotent

end DrazinMPProjectorData

/-- Named commutator obstruction packet. -/
@[rep_depth transport]
structure ProjectorCommutatorObstruction (R : Type*) [Ring R] where
  pair : ProjectorPair R
  noncommutingSplit : pair.commutator ≠ 0

theorem ProjectorCommutatorObstruction.implies_mismatch
    (O : ProjectorCommutatorObstruction R) :
    O.pair.mismatch ≠ 0 :=
  ProjectorPair.commutator_ne_zero_implies_mismatch_ne_zero (P := O.pair) O.noncommutingSplit

end InfoGeometry.Canonical.OperatorProjectorMismatch

import Mathlib
import InfoGeometry.Meta.Architecture

/-!
# Chiral KMS owner

KMS/modular dynamics preserve chirality exactly when the generator commutes with
an explicitly supplied chiral grading.  This module proves preservation versus
obstruction only; no uniqueness theorem for the KMS flow is asserted.
-/

namespace InfoGeometry.Canonical.ChiralKMSOwner

variable {R : Type*} [Ring R]

/-- Chiral grading witness. -/
@[rep_depth thermo]
structure ChiralGrading where
  Γ5 : R
  involutive : Γ5 * Γ5 = 1

/-- KMS/modular generator preserves chirality iff it commutes with Γ₅. -/
def KMSPreservesChirality (K : R) (Γ : ChiralGrading (R := R)) : Prop :=
  K * Γ.Γ5 = Γ.Γ5 * K

/-- Algebraic obstruction to preserving the L/R decomposition. -/
def ChiralKMSObstruction (K : R) (Γ : ChiralGrading (R := R)) : R :=
  K * Γ.Γ5 - Γ.Γ5 * K

/-- Preservation is equivalent to vanishing chiral obstruction. -/
theorem KMSPreservesChirality_iff_obstruction_zero
    (K : R) (Γ : ChiralGrading (R := R)) :
    KMSPreservesChirality K Γ ↔ ChiralKMSObstruction K Γ = 0 := by
  constructor
  · intro h
    exact sub_eq_zero.mpr h
  · intro h
    exact sub_eq_zero.mp h

/-- No-uniqueness packet: a flow witness only records preservation/obstruction. -/
@[rep_depth thermo]
structure ChiralKMSFlowWitness where
  K : R
  Γ : ChiralGrading (R := R)
  preservesOrObstructs : KMSPreservesChirality K Γ ∨ ChiralKMSObstruction K Γ ≠ 0

end InfoGeometry.Canonical.ChiralKMSOwner

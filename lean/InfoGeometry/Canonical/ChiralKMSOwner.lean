import Mathlib.Tactic
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

/-- Multiplicative thermal shift: a modular step followed by a Wick/phase factor. -/
def thermalShift (modularStep wickFactor : R) : R :=
  modularStep * wickFactor

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

/-- The identity thermal step preserves chirality. -/
theorem KMSPreservesChirality_one (Γ : ChiralGrading (R := R)) :
    KMSPreservesChirality (1 : R) Γ := by
  simp [KMSPreservesChirality]

/--
Two chirality-preserving factors have a chirality-preserving product.

This is the algebraic core behind the Wick/KMS protection statement: no
matrix exponential or Type-III trace is manufactured here; both factors must
already commute with the supplied grading.
-/
theorem KMSPreservesChirality_mul
    {K W : R} {Γ : ChiralGrading (R := R)}
    (hK : KMSPreservesChirality K Γ)
    (hW : KMSPreservesChirality W Γ) :
    KMSPreservesChirality (K * W) Γ := by
  unfold KMSPreservesChirality at hK hW ⊢
  calc
    (K * W) * Γ.Γ5 = K * (W * Γ.Γ5) := by simp [mul_assoc]
    _ = K * (Γ.Γ5 * W) := by rw [hW]
    _ = (K * Γ.Γ5) * W := by simp [mul_assoc]
    _ = (Γ.Γ5 * K) * W := by rw [hK]
    _ = Γ.Γ5 * (K * W) := by simp [mul_assoc]

/--
If a modular step and a Wick/phase factor both commute with chirality, their
thermal shift preserves chirality.
-/
theorem thermalShift_preserves_chirality
    {K W : R} {Γ : ChiralGrading (R := R)}
    (hK : KMSPreservesChirality K Γ)
    (hW : KMSPreservesChirality W Γ) :
    KMSPreservesChirality (thermalShift K W) Γ := by
  simpa [thermalShift] using KMSPreservesChirality_mul (R := R) hK hW

/-! A flow witness is the direct existential proposition it expresses; no
record is needed merely to store the two carriers and their disjunction. -/
def ChiralKMSFlowWitness : Prop :=
  ∃ K : R, ∃ Γ : ChiralGrading (R := R),
    KMSPreservesChirality K Γ ∨ ChiralKMSObstruction K Γ ≠ 0

end InfoGeometry.Canonical.ChiralKMSOwner

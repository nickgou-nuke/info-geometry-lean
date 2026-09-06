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

/-- KMS/modular generator preserves chirality iff it commutes with Γ₅. -/
def KMSPreservesChirality (K Γ5 : R) : Prop :=
  K * Γ5 = Γ5 * K

/-- Multiplicative thermal shift: a modular step followed by a Wick/phase factor. -/
def thermalShift (modularStep wickFactor : R) : R :=
  modularStep * wickFactor

/-- Algebraic obstruction to preserving the L/R decomposition. -/
def ChiralKMSObstruction (K Γ5 : R) : R :=
  K * Γ5 - Γ5 * K

/-- Preservation is equivalent to vanishing chiral obstruction. -/
theorem KMSPreservesChirality_iff_obstruction_zero
    (K Γ5 : R) :
    KMSPreservesChirality K Γ5 ↔ ChiralKMSObstruction K Γ5 = 0 := by
  constructor
  · intro h
    exact sub_eq_zero.mpr h
  · intro h
    exact sub_eq_zero.mp h

/-- The identity thermal step preserves chirality. -/
theorem KMSPreservesChirality_one (Γ5 : R) :
    KMSPreservesChirality (1 : R) Γ5 := by
  simp [KMSPreservesChirality]

/--
Two chirality-preserving factors have a chirality-preserving product.

This is the algebraic core behind the Wick/KMS protection statement: no
matrix exponential or Type-III trace is manufactured here; both factors must
already commute with the supplied grading.
-/
theorem KMSPreservesChirality_mul
    {K W Γ5 : R}
    (hK : KMSPreservesChirality K Γ5)
    (hW : KMSPreservesChirality W Γ5) :
    KMSPreservesChirality (K * W) Γ5 := by
  unfold KMSPreservesChirality at hK hW ⊢
  calc
    (K * W) * Γ5 = K * (W * Γ5) := by simp [mul_assoc]
    _ = K * (Γ5 * W) := by rw [hW]
    _ = (K * Γ5) * W := by simp [mul_assoc]
    _ = (Γ5 * K) * W := by rw [hK]
    _ = Γ5 * (K * W) := by simp [mul_assoc]

/--
If a modular step and a Wick/phase factor both commute with chirality, their
thermal shift preserves chirality.
-/
theorem thermalShift_preserves_chirality
    {K W Γ5 : R}
    (hK : KMSPreservesChirality K Γ5)
    (hW : KMSPreservesChirality W Γ5) :
    KMSPreservesChirality (thermalShift K W) Γ5 := by
  simpa [thermalShift] using KMSPreservesChirality_mul (R := R) hK hW

end InfoGeometry.Canonical.ChiralKMSOwner

import InfoGeometry.Canonical.CanonicalZornOuterTrialityGroup
import InfoGeometry.Canonical.CanonicalZornSpinVectorAction

/-!
# Candidate reflection for Cartan's related-triples triality group

This file investigates the order-two reflection missing from the cyclic
related-triples action.  The reflection exchanges the vector and positive
spinor slots and applies the canonical Zorn conjugation to all three slots.
It acts on actual invertible maps on the three typed carriers; it is not a
permutation of sector labels.

This is a candidate owner and is intentionally not registered in the public
build until its proofs have passed the repository's locked verification flow.
-/

noncomputable section

namespace CanonicalZornOuterTrialityReflectionCandidate

open CanonicalZornCompositionTriality
open CanonicalZornOuterTrialityGroup
open InfoGeometry.Canonical.CanonicalZornTrialitySpinEquivariance
open InfoGeometry.Canonical.CanonicalZornSpinVectorAction
open InfoGeometry.Physics.SplitOctonionBraidSU3

/-- Conjugate-linear-slot transport from the positive spinor copy to the
vector copy.  The map is complex-linear because Zorn conjugation is complex
linear on the split-octonion carrier. -/
def spinorPlusToVectorReflection : SpinorPlus8 ≃ₗ[ℂ] Vector8 :=
  (copyConjLinearEquiv .spinorPlus).trans
    (spinorPlusToSpinorMinus.trans spinorMinusToVector)

/-- Conjugate-linear-slot transport from the vector copy to the positive
spinor copy. -/
def vectorToSpinorPlusReflection : Vector8 ≃ₗ[ℂ] SpinorPlus8 :=
  (copyConjLinearEquiv .vector).trans vectorToSpinorPlus

/-- Conjugation on the negative-spinor slot. -/
abbrev spinorMinusReflection : SpinorMinus8 ≃ₗ[ℂ] SpinorMinus8 :=
  copyConjLinearEquiv .spinorMinus

@[simp] theorem spinorPlusToVectorReflection_val (S : SpinorPlus8) :
    (spinorPlusToVectorReflection S).val = zornConj S.val := by
  apply zornCoordinates_injective
  simp [spinorPlusToVectorReflection, copyConjLinearEquiv,
    spinorPlusToSpinorMinus, spinorMinusToVector,
    copyLinearEquivCoordinates, copyEquivCoordinates,
    coordinatesToZorn_zornCoordinates]

@[simp] theorem vectorToSpinorPlusReflection_val (V : Vector8) :
    (vectorToSpinorPlusReflection V).val = zornConj V.val := by
  apply zornCoordinates_injective
  simp [vectorToSpinorPlusReflection, copyConjLinearEquiv,
    vectorToSpinorPlus, copyLinearEquivCoordinates,
    copyEquivCoordinates, coordinatesToZorn_zornCoordinates]

@[simp] theorem spinorMinusReflection_val (C : SpinorMinus8) :
    (spinorMinusReflection C).val = zornConj C.val := by
  exact copyConjLinearEquiv_apply C

theorem spinorPlusToVectorReflection_norm (S : SpinorPlus8) :
    vectorNorm (spinorPlusToVectorReflection S) = spinorPlusNorm S := by
  simp [vectorNorm, spinorPlusNorm, zornNorm_conj]

theorem vectorToSpinorPlusReflection_norm (V : Vector8) :
    spinorPlusNorm (vectorToSpinorPlusReflection V) = vectorNorm V := by
  simp [vectorNorm, spinorPlusNorm, zornNorm_conj]

theorem spinorMinusReflection_norm (C : SpinorMinus8) :
    spinorMinusNorm (spinorMinusReflection C) = spinorMinusNorm C := by
  simp [spinorMinusReflection, spinorMinusNorm, zornNorm_conj]

/-- Zorn trace is unchanged by the canonical conjugation. -/
theorem zornTrace_conj_candidate (X : Zorn) :
    zornTrace (zornConj X) = zornTrace X := by
  simp [zornTrace, zornConj, add_comm]

/-- Scalar trace is insensitive to reassociation of a triple Zorn product.
This is the associator-trace identity needed to reverse Cartan's trilinear
form under conjugation. -/
theorem zornTrace_mul_assoc_candidate (X Y Z : Zorn) :
    zornTrace (zornMul (zornMul X Y) Z) =
      zornTrace (zornMul X (zornMul Y Z)) := by
  simp [zornTrace, zornMul, dot3, cross3]
  ring

/-- The conjugate slot swap preserves the actual Zorn trilinear form. -/
theorem reflection_preserves_trialityForm
    (V : Vector8) (S : SpinorPlus8) (C : SpinorMinus8) :
    trialityForm (spinorPlusToVectorReflection S)
        (vectorToSpinorPlusReflection V) (spinorMinusReflection C) =
      trialityForm V S C := by
  change zornTrace
      (zornMul
        (zornMul (zornConj S.val) (zornConj V.val))
        (zornConj C.val)) =
    zornTrace (zornMul (zornMul V.val S.val) C.val)
  calc
    zornTrace
        (zornMul
          (zornMul (zornConj S.val) (zornConj V.val))
          (zornConj C.val)) =
        zornTrace
          (zornMul
            (zornMul (zornConj C.val) (zornConj S.val))
            (zornConj V.val)) := by
              rw [zornTripleTrace_cyclic]
              rw [zornTripleTrace_cyclic]
    _ = zornTrace
          (zornMul (zornConj C.val)
            (zornMul (zornConj S.val) (zornConj V.val))) :=
          zornTrace_mul_assoc_candidate _ _ _
    _ = zornTrace
          (zornConj (zornMul (zornMul V.val S.val) C.val)) := by
          rw [zornConj_mul, zornConj_mul]
    _ = zornTrace (zornMul (zornMul V.val S.val) C.val) :=
          zornTrace_conj_candidate _

/-! The remaining declarations will package this reflection on `TrialityGL`,
restrict it to `CartanTrialityGroup`, and prove the involution and Coxeter
relations against `cartanTrialityCycle`.  No group-action theorem is exposed
until those proofs have been checked in Lean.
-/

end CanonicalZornOuterTrialityReflectionCandidate

end noncomputable section

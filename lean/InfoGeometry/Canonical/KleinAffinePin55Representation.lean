import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Canonical.KleinAffinePin55RealizationBridge
import InfoGeometry.Clifford.Cl55RealSplitPinKernelBridge

/-!
# The native affine Pin(5,5) realization of the Klein presentation

The presented Klein group is sent to the existing affine semidirect product
by a reflection glide and a translation in a reflected Witt direction.  This
is an algebraic representation only; no fundamental-group identification is
asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinAffinePin55Representation

open InfoGeometry.Canonical.AffinePin55Cover
open InfoGeometry.Canonical.KleinAffinePin55RealizationBridge
open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.Clifford.Clifford55

def affineKleinReflection : realSplitPin55 := fNegRealPin 0

def affineKleinTranslationVector : V55 := f_neg 0

theorem affineKleinReflection_negates_translationVector :
    (realSplitPinAction affineKleinReflection)
        (Multiplicative.ofAdd affineKleinTranslationVector) =
      Multiplicative.ofAdd (-affineKleinTranslationVector) := by
  apply Multiplicative.ext
  change (realSplitPinOrthogonalAction affineKleinReflection :
      V55 ≃ₗ[ℝ] V55) affineKleinTranslationVector =
        -affineKleinTranslationVector
  change (realSplitPinOrthogonalAction (fNegRealPin 0) :
      V55 ≃ₗ[ℝ] V55) (f_neg 0) = -(f_neg 0)
  rw [realSplitPinOrthogonalAction_fNegRealPin]
  simp [coordinateReflectionGenerator, negativeReflectionLinearEquiv_apply,
    negativeReflection_apply_f_neg]

def affineKleinA : AffinePin55Native :=
  affinePinGlide 0 affineKleinReflection

def affineKleinB : AffinePin55Native :=
  affinePinGlide affineKleinTranslationVector 1

theorem affineKlein_conjugation_relation :
    affineKleinA * affineKleinB * affineKleinA⁻¹ = affineKleinB⁻¹ := by
  rw [affineKleinA, affineKleinB, affinePin_conj_translation]
  rw [affineKleinReflection_negates_translationVector]
  simp [affinePinGlide]

def affineKleinRepresentation : KleinGroup →* AffinePin55Native :=
  kleinRep affineKleinA affineKleinB affineKlein_conjugation_relation

theorem affineKleinRepresentation_generators :
    affineKleinRepresentation (toKlein genA) = affineKleinA ∧
    affineKleinRepresentation (toKlein genB) = affineKleinB := by
  exact kleinRep_relator_relation affineKleinA affineKleinB
    affineKlein_conjugation_relation

theorem affineKleinRepresentation_nontrivial :
    affineKleinRepresentation (toKlein genB) ≠ 1 := by
  rw [affineKleinRepresentation_generators.2]
  intro h
  have hleft := congrArg SemidirectProduct.left h
  change Multiplicative.ofAdd affineKleinTranslationVector = 1 at hleft
  have hvec : affineKleinTranslationVector = 0 := by
    exact Multiplicative.ext_iff.mp hleft
  have hcoord := congrArg (fun x : V55 => x.2 0) hvec
  simp [affineKleinTranslationVector, f_neg] at hcoord

end InfoGeometry.Canonical.KleinAffinePin55Representation

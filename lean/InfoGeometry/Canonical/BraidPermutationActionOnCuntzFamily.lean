/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CuntzWordMonomialKMSFunctional
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Physics.B3PresentedGroup
import InfoGeometry.Physics.JonesBraidB3

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Physics.B3PresentedGroup

/-!
# Word-level braid permutation

This owner proves only the finite word-level Artin relation.  It does not
claim an automorphism of the Cuntz algebra or invariance of a KMS state: the
former requires a conjugation/automorphism definition, not left multiplication
by a word isometry.
-/

/-- The permutation of the first two generator labels induced by `σ₁`. -/
def braidSigma1LetterEquiv : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

/-- The permutation of the last two generator labels induced by `σ₂`. -/
def braidSigma2LetterEquiv : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

/-- Apply `σ₁` to every generator label in a Cuntz word. -/
def braidSigma1Action (w : CuntzWord3) : CuntzWord3 :=
  w.map braidSigma1LetterEquiv

/-- Apply `σ₂` to every generator label in a Cuntz word. -/
def braidSigma2Action (w : CuntzWord3) : CuntzWord3 :=
  w.map braidSigma2LetterEquiv

/-- Braid relation: σ₁σ₂σ₁ = σ₂σ₁σ₂ -/
theorem braidRelation (w : CuntzWord3) :
    braidSigma1Action (braidSigma2Action (braidSigma1Action w)) =
    braidSigma2Action (braidSigma1Action (braidSigma2Action w)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have htail :
        List.map braidSigma1LetterEquiv
            (List.map braidSigma2LetterEquiv
              (List.map braidSigma1LetterEquiv w)) =
          List.map braidSigma2LetterEquiv
            (List.map braidSigma1LetterEquiv
              (List.map braidSigma2LetterEquiv w)) := by
      simpa [braidSigma1Action, braidSigma2Action] using ih
    simp only [braidSigma1Action, braidSigma2Action, List.map_cons]
    rw [htail]
    congr 1
    fin_cases i <;> decide

end InfoGeometry.Canonical

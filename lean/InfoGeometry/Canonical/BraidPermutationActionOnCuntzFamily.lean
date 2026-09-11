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

/-- The action of σ₁ on word monomials: σ₁·S_{i}w = S_{τ₁(i)}σ₁·w -/
def braidSigma1Action (w : CuntzWord3) : CuntzWord3 :=
  match w with
  | [] => []
  | (⟨0, _⟩ :: w) => (⟨1, by decide⟩ :: w)
  | (⟨1, _⟩ :: w) => (⟨0, by decide⟩ :: w)
  | (⟨2, _⟩ :: w) => (⟨2, by decide⟩ :: w)

/-- The action of σ₂ on word monomials: σ₂·S_{i}w = S_{τ₂(i)}σ₂·w -/
def braidSigma2Action (w : CuntzWord3) : CuntzWord3 :=
  match w with
  | [] => []
  | (⟨0, _⟩ :: w) => (⟨0, by decide⟩ :: w)
  | (⟨1, _⟩ :: w) => (⟨2, by decide⟩ :: w)
  | (⟨2, _⟩ :: w) => (⟨1, by decide⟩ :: w)

/-- Braid relation: σ₁σ₂σ₁ = σ₂σ₁σ₂ -/
theorem braidRelation (w : CuntzWord3) :
    braidSigma1Action (braidSigma2Action (braidSigma1Action w)) =
    braidSigma2Action (braidSigma1Action (braidSigma2Action w)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    fin_cases i <;> simp [braidSigma1Action, braidSigma2Action, ih]
    <;> rfl

end InfoGeometry.Canonical

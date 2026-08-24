import Mathlib.GroupTheory.PresentedGroup

/-!
# The three-strand braid group as a presented group

This file defines `B₃` from two generators and the single Artin relation

`σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`.

It also exposes the universal mapping property needed by concrete braid
representations.  No positive-monoid localization, Garside normal form,
configuration-space fibration, or Weyl-group quotient is asserted here.
-/

namespace InfoGeometry.Categorical.BraidThreePresentedGroup

/-- The two standard generators of the three-strand braid group. -/
inductive Generator where
  | sigmaOne
  | sigmaTwo
  deriving DecidableEq

/-- The relator `σ₁ σ₂ σ₁ (σ₂ σ₁ σ₂)⁻¹`. -/
def artinRelator : FreeGroup Generator :=
  FreeGroup.of .sigmaOne *
    FreeGroup.of .sigmaTwo *
      FreeGroup.of .sigmaOne *
        (FreeGroup.of .sigmaTwo *
          FreeGroup.of .sigmaOne *
            FreeGroup.of .sigmaTwo)⁻¹

/-- The singleton set containing the three-strand Artin relator. -/
def relations : Set (FreeGroup Generator) :=
  {artinRelator}

/-- The three-strand braid group `B₃` as a native Mathlib presented group. -/
abbrev BraidGroup3 := PresentedGroup relations

/-- The first standard generator of `B₃`. -/
def sigmaOne : BraidGroup3 :=
  PresentedGroup.of Generator.sigmaOne

/-- The second standard generator of `B₃`. -/
def sigmaTwo : BraidGroup3 :=
  PresentedGroup.of Generator.sigmaTwo

/-- The defining Artin relation in the presented group. -/
theorem artin_relation :
    sigmaOne * sigmaTwo * sigmaOne =
      sigmaTwo * sigmaOne * sigmaTwo := by
  apply eq_of_mul_inv_eq_one
  simpa [sigmaOne, sigmaTwo, artinRelator] using
    (PresentedGroup.one_of_mem
      (rels := relations) (x := artinRelator)
      (by simp [relations]))

/-- The standard Garside half-twist word in `B₃`.

Only the group element is defined here.  No claim about a Weyl-group image or
sheet involution is made without a separate quotient/intertwining theorem.
-/
def garsideDelta : BraidGroup3 :=
  sigmaOne * sigmaTwo * sigmaOne

@[simp]
theorem garsideDelta_eq_alternate :
    garsideDelta = sigmaTwo * sigmaOne * sigmaTwo := by
  simpa [garsideDelta] using artin_relation

/-- Two elements of a group satisfying the three-strand Artin relation. -/
structure ArtinPair (G : Type*) [Group G] where
  sigmaOne : G
  sigmaTwo : G
  artin : sigmaOne * sigmaTwo * sigmaOne =
    sigmaTwo * sigmaOne * sigmaTwo

namespace ArtinPair

variable {G : Type*} [Group G]

/-- The map from abstract braid generators to a concrete Artin pair. -/
def generatorMap (P : ArtinPair G) : Generator → G
  | .sigmaOne => P.sigmaOne
  | .sigmaTwo => P.sigmaTwo

/-- The unique relator evaluates to the identity for an Artin pair. -/
theorem relator_eq_one (P : ArtinPair G) :
    ∀ r ∈ relations,
      FreeGroup.lift P.generatorMap r = 1 := by
  intro r hr
  have hr' : r = artinRelator := by
    simpa [relations] using hr
  subst r
  simp [artinRelator, generatorMap, P.artin]

/-- The universal group homomorphism from `B₃` determined by an Artin pair. -/
def toBraidGroupHom (P : ArtinPair G) :
    BraidGroup3 →* G :=
  PresentedGroup.toGroup P.relator_eq_one

@[simp]
theorem toBraidGroupHom_sigmaOne (P : ArtinPair G) :
    P.toBraidGroupHom sigmaOne = P.sigmaOne := by
  exact PresentedGroup.toGroup.of P.relator_eq_one

@[simp]
theorem toBraidGroupHom_sigmaTwo (P : ArtinPair G) :
    P.toBraidGroupHom sigmaTwo = P.sigmaTwo := by
  exact PresentedGroup.toGroup.of P.relator_eq_one

/-- The universal map is the unique group homomorphism with the prescribed
generator values. -/
theorem toBraidGroupHom_unique
    (P : ArtinPair G)
    (f : BraidGroup3 →* G)
    (hOne : f sigmaOne = P.sigmaOne)
    (hTwo : f sigmaTwo = P.sigmaTwo) :
    f = P.toBraidGroupHom := by
  apply PresentedGroup.ext
  intro g
  cases g
  · exact hOne
  · exact hTwo

/-- Inverse generators satisfy the inverse Artin relation automatically. -/
theorem inverse_artin (P : ArtinPair G) :
    P.sigmaOne⁻¹ * P.sigmaTwo⁻¹ * P.sigmaOne⁻¹ =
      P.sigmaTwo⁻¹ * P.sigmaOne⁻¹ * P.sigmaTwo⁻¹ := by
  simpa using congrArg Inv.inv P.artin

end ArtinPair

end InfoGeometry.Categorical.BraidThreePresentedGroup

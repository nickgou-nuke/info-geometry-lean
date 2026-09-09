import Mathlib.GroupTheory.PresentedGroup

/-! The three-strand Artin group, exposed through Mathlib's presented-group
universal property.  This owner contains only the braid presentation and its
universal evaluation map. -/

namespace InfoGeometry.Categorical.BraidThreePresentedGroup

inductive Generator where
  | sigmaOne
  | sigmaTwo
  deriving DecidableEq

def artinRelator : FreeGroup Generator :=
  FreeGroup.of .sigmaOne * FreeGroup.of .sigmaTwo * FreeGroup.of .sigmaOne *
    (FreeGroup.of .sigmaTwo * FreeGroup.of .sigmaOne * FreeGroup.of .sigmaTwo)⁻¹

def relations : Set (FreeGroup Generator) := {artinRelator}

abbrev BraidGroup3 := PresentedGroup relations

def sigmaOne : BraidGroup3 := PresentedGroup.of Generator.sigmaOne
def sigmaTwo : BraidGroup3 := PresentedGroup.of Generator.sigmaTwo

theorem artin_relation :
    sigmaOne * sigmaTwo * sigmaOne = sigmaTwo * sigmaOne * sigmaTwo := by
  apply eq_of_mul_inv_eq_one
  simpa [sigmaOne, sigmaTwo, artinRelator] using
    (PresentedGroup.one_of_mem (rels := relations) (x := artinRelator)
      (by simp [relations]))

def garsideDelta : BraidGroup3 := sigmaOne * sigmaTwo * sigmaOne

@[simp] theorem garsideDelta_eq_alternate :
    garsideDelta = sigmaTwo * sigmaOne * sigmaTwo := by
  simpa [garsideDelta] using artin_relation

structure ArtinPair (G : Type*) [Group G] where
  sigmaOne : G
  sigmaTwo : G
  artin : sigmaOne * sigmaTwo * sigmaOne = sigmaTwo * sigmaOne * sigmaTwo

namespace ArtinPair

variable {G : Type*} [Group G]

def generatorMap (P : ArtinPair G) : Generator → G
  | .sigmaOne => P.sigmaOne
  | .sigmaTwo => P.sigmaTwo

theorem relator_eq_one (P : ArtinPair G) :
    ∀ r ∈ relations, FreeGroup.lift P.generatorMap r = 1 := by
  intro r hr
  have hr' : r = artinRelator := by simpa [relations] using hr
  subst r
  calc
    (FreeGroup.lift P.generatorMap) artinRelator =
        (P.sigmaOne * P.sigmaTwo * P.sigmaOne) *
          (P.sigmaTwo * P.sigmaOne * P.sigmaTwo)⁻¹ := by
      simp [artinRelator, generatorMap, mul_assoc]
    _ = 1 := by rw [← P.artin]; simp [mul_assoc]

def toBraidGroupHom (P : ArtinPair G) : BraidGroup3 →* G :=
  PresentedGroup.toGroup P.relator_eq_one

@[simp] theorem toBraidGroupHom_sigmaOne (P : ArtinPair G) :
    P.toBraidGroupHom
        InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaOne = P.sigmaOne :=
  PresentedGroup.toGroup.of P.relator_eq_one

@[simp] theorem toBraidGroupHom_sigmaTwo (P : ArtinPair G) :
    P.toBraidGroupHom
        InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaTwo = P.sigmaTwo :=
  PresentedGroup.toGroup.of P.relator_eq_one

theorem toBraidGroupHom_unique (P : ArtinPair G) (f : BraidGroup3 →* G)
    (hOne : f InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaOne = P.sigmaOne)
    (hTwo : f InfoGeometry.Categorical.BraidThreePresentedGroup.sigmaTwo = P.sigmaTwo) :
    f = P.toBraidGroupHom := by
  apply PresentedGroup.ext
  intro g
  cases g
  · change f BraidThreePresentedGroup.sigmaOne =
      P.toBraidGroupHom BraidThreePresentedGroup.sigmaOne
    rw [toBraidGroupHom_sigmaOne P]
    exact hOne
  · change f BraidThreePresentedGroup.sigmaTwo =
      P.toBraidGroupHom BraidThreePresentedGroup.sigmaTwo
    rw [toBraidGroupHom_sigmaTwo P]
    exact hTwo

theorem inverse_artin (P : ArtinPair G) :
    P.sigmaOne⁻¹ * P.sigmaTwo⁻¹ * P.sigmaOne⁻¹ =
      P.sigmaTwo⁻¹ * P.sigmaOne⁻¹ * P.sigmaTwo⁻¹ := by
  simpa [mul_assoc] using congrArg Inv.inv P.artin

end ArtinPair
end InfoGeometry.Categorical.BraidThreePresentedGroup

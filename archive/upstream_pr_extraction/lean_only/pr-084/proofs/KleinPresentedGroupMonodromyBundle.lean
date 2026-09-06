import proofs.KleinFundamentalGroup
import proofs.KleinAffineDeckGroup
import proofs.KleinPresentedGroup
import proofs.KleinProjectiveAssociatedBundleCore
import proofs.KleinGlideCovering

noncomputable section
namespace KleinPresentedGroupMonodromyBundle

open KleinFundamentalGroup
open KleinPresentedGroup
open KleinAffineDeckGroup
open KleinProjectiveAssociatedBundleCore
open KleinGlideCovering
open KleinProjectiveSixState

/-- The affine normal form maps to `Deck2` by parity of its `a`-component. -/
def affineToDeck2 (g : AffineKleinGroup) : Deck2 :=
  (parityHom g.2).toAdd

@[simp] theorem affineToDeck2_a :
    affineToDeck2 aGen = 1 := by
  native_decide

@[simp] theorem affineToDeck2_b :
    affineToDeck2 bGen = 0 := by
  native_decide

/-- Forget to the presented `KleinGroup` through the affine identification. -/
def presentedToDeck2 : KleinPresentedGroup.KleinGroup → Deck2 :=
  fun g => affineToDeck2 (KleinAffineDeckGroup.presentedToAffine g)

@[simp] theorem presentedToDeck2_genA :
    presentedToDeck2 (toKlein genA) = (1 : Deck2) := by
  rw [presentedToDeck2, KleinAffineDeckGroup.presentedToAffine_a]
  simp

@[simp] theorem presentedToDeck2_genB :
    presentedToDeck2 (toKlein genB) = (0 : Deck2) := by
  rw [presentedToDeck2, KleinAffineDeckGroup.presentedToAffine_b]
  simp

/-- The presented-group monodromy on the projective six-state fibre. -/
def presentedBundleMonodromy (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    KleinPresentedGroup.KleinGroup →
      KleinProjectiveSixState.ProjectiveSixState →
        KleinProjectiveSixState.ProjectiveSixState :=
  fun g q => projectiveDeckMap omega homega (presentedToDeck2 g) q

@[simp] theorem presentedBundleMonodromy_genA
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (q : KleinProjectiveSixState.ProjectiveSixState) :
    presentedBundleMonodromy omega homega (toKlein genA) q =
      projectiveTheta omega homega q := by
  rw [presentedBundleMonodromy, presentedToDeck2_genA]
  simp [projectiveDeckMap]

@[simp] theorem presentedBundleMonodromy_genB
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (q : KleinProjectiveSixState.ProjectiveSixState) :
    presentedBundleMonodromy omega homega (toKlein genB) q = q := by
  rw [presentedBundleMonodromy, presentedToDeck2_genB]
  simp [projectiveDeckMap]

/-- `π₁`-monodromy obtained by transport through the presented-group equivalence. -/
def piOneToDeck2 : KleinFundamentalGroup.KleinPiOne → Deck2 :=
  fun p => presentedToDeck2 (fundamentalGroupEquivPresented p)

def piOneBundleMonodromy (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    KleinFundamentalGroup.KleinPiOne →
      KleinProjectiveSixState.ProjectiveSixState →
        KleinProjectiveSixState.ProjectiveSixState :=
  fun p q => projectiveDeckMap omega homega (piOneToDeck2 p) q

@[simp] theorem piOneBundleMonodromy_of_a
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (q : KleinProjectiveSixState.ProjectiveSixState) :
    piOneBundleMonodromy omega homega
        (fundamentalGroupEquivPresented.symm (toKlein genA)) q =
      projectiveTheta omega homega q := by
  change projectiveDeckMap omega homega
      (presentedToDeck2 (fundamentalGroupEquivPresented
        (fundamentalGroupEquivPresented.symm (toKlein genA)))) q =
    projectiveTheta omega homega q
  simpa [presentedToDeck2, presentedBundleMonodromy,
      fundamentalGroupEquivPresented.apply_symm_apply] using
    (presentedBundleMonodromy_genA omega homega q)

@[simp] theorem piOneBundleMonodromy_of_b
    (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0)
    (q : KleinProjectiveSixState.ProjectiveSixState) :
    piOneBundleMonodromy omega homega
        (fundamentalGroupEquivPresented.symm (toKlein genB)) q = q := by
  change projectiveDeckMap omega homega
      (presentedToDeck2 (fundamentalGroupEquivPresented
        (fundamentalGroupEquivPresented.symm (toKlein genB)))) q = q
  simpa [presentedToDeck2, presentedBundleMonodromy,
      fundamentalGroupEquivPresented.apply_symm_apply] using
    (presentedBundleMonodromy_genB omega homega q)

end KleinPresentedGroupMonodromyBundle
end noncomputable section

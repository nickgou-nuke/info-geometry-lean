import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Categorical.GrothendieckCompletionFunctor

/-!
# Canonical Grothendieck completion bridge

The pinned Mathlib version does not expose the former `Algebra.GrothendieckAddGroup`
API. The repository-owned quotient completion is the canonical owner; this module
exposes its categorical functor directly and proves the identity natural
isomorphism without introducing a parallel completion.
-/

noncomputable section

universe u

namespace InfoGeometry.Algebra.GrothendieckMathlibNatIso

open CategoryTheory

abbrev mathlibGrothendieckFunctor :
    AddCommMonCat.{u} ⥤ AddCommGrpCat.{u} :=
  InfoGeometry.Categorical.grothendieckCompletionFunctor

abbrev grothendieckFunctorNatIso :
    InfoGeometry.Categorical.grothendieckCompletionFunctor ≅
      mathlibGrothendieckFunctor :=
  Iso.refl _

@[simp] theorem grothendieckFunctorNatIso_hom_app (M : AddCommMonCat.{u}) :
    (grothendieckFunctorNatIso.hom.app M).hom' =
      (InfoGeometry.Categorical.grothendieckCompletionFunctor.map
        (𝟙 M)).hom' := by
  simp

theorem grothendieckFunctorNatIso_naturality
    {M N : AddCommMonCat.{u}} (f : M ⟶ N) :
    InfoGeometry.Categorical.grothendieckCompletionFunctor.map f ≫
        grothendieckFunctorNatIso.hom.app N =
      grothendieckFunctorNatIso.hom.app M ≫
        mathlibGrothendieckFunctor.map f := by
  simpa using (grothendieckFunctorNatIso.hom.naturality f)

end InfoGeometry.Algebra.GrothendieckMathlibNatIso

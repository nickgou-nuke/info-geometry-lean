import Mathlib.Algebra.Category.Grp.AB
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Grothendieck

/-!
# The categorical Grothendieck-completion functor

This is the categorical packaging of the additive completion owned by
`InfoGeometry.Algebra.Grothendieck`.  The object map is the quotient
completion, while the morphism map is the already-proved induced additive
homomorphism.  No second completion construction is introduced here.
-/

universe u

namespace InfoGeometry.Categorical

open CategoryTheory

noncomputable def grothendieckCompletionFunctor :
    AddCommMonCat.{u} ⥤ AddCommGrpCat.{u} where
  obj M := AddCommGrpCat.of (Grothendieck (M : Type u))
  map f := AddCommGrpCat.homAddEquiv.symm (grothendieckFunctor f.hom')
  map_id M := by
    apply AddCommGrpCat.hom_ext
    change grothendieckFunctor ((𝟙 M : M ⟶ M).hom') = _
    simpa using (grothendieckFunctor_id (M := (M : Type u)))
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    change grothendieckFunctor ((f ≫ g).hom') = _
    simpa using (grothendieckFunctor_comp f.hom' g.hom')

@[simp]
theorem grothendieckCompletionFunctor_obj_carrier
    (M : AddCommMonCat.{u}) :
    (grothendieckCompletionFunctor.obj M : Type u) = Grothendieck (M : Type u) := rfl

@[simp]
theorem grothendieckCompletionFunctor_map_hom
    {M N : AddCommMonCat.{u}} (f : M ⟶ N) :
    (grothendieckCompletionFunctor.map f).hom' = grothendieckFunctor f.hom' := by
  rfl

end InfoGeometry.Categorical

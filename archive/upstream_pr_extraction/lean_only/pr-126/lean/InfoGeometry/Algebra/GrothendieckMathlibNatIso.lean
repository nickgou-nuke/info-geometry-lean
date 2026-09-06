import Mathlib.Algebra.Category.Grp.AB
import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Categorical.GrothendieckCompletionFunctor

noncomputable section

universe u

namespace InfoGeometry.Algebra.GrothendieckMathlibNatIso

open CategoryTheory

noncomputable def mathlibGrothendieckMap
    {M N : Type u} [AddCommMonoid M] [AddCommMonoid N] (f : M →+ N) :
    Algebra.GrothendieckAddGroup M →+ Algebra.GrothendieckAddGroup N :=
  Algebra.GrothendieckAddGroup.lift
    ((Algebra.GrothendieckAddGroup.of).comp f)

@[simp] theorem mathlibGrothendieckMap_of
    {M N : Type u} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) (m : M) :
    mathlibGrothendieckMap f (Algebra.GrothendieckAddGroup.of m) =
      Algebra.GrothendieckAddGroup.of (f m) := by
  exact mathlibGrothendieckLift_of ((Algebra.GrothendieckAddGroup.of).comp f) m

@[simp] theorem mathlibGrothendieckMap_id (M : Type u) [AddCommMonoid M] :
    mathlibGrothendieckMap (AddMonoidHom.id M) = AddMonoidHom.id _ := by
  apply (Algebra.GrothendieckAddGroup.lift
    (M := M) (G := Algebra.GrothendieckAddGroup M)).symm.injective
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply,
    Algebra.GrothendieckAddGroup.lift_symm_apply]
  ext m
  exact mathlibGrothendieckMap_of (AddMonoidHom.id M) m

@[simp] theorem mathlibGrothendieckMap_comp
    {M N P : Type u} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    (f : M →+ N) (g : N →+ P) :
    mathlibGrothendieckMap (g.comp f) =
      (mathlibGrothendieckMap g).comp (mathlibGrothendieckMap f) := by
  apply (Algebra.GrothendieckAddGroup.lift
    (M := M) (G := Algebra.GrothendieckAddGroup P)).symm.injective
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply,
    Algebra.GrothendieckAddGroup.lift_symm_apply]
  ext m
  change mathlibGrothendieckMap (g.comp f)
      (Algebra.GrothendieckAddGroup.of m) =
    mathlibGrothendieckMap g
      (mathlibGrothendieckMap f (Algebra.GrothendieckAddGroup.of m))
  rw [mathlibGrothendieckMap_of, mathlibGrothendieckMap_of,
    mathlibGrothendieckMap_of]
  rfl

noncomputable def mathlibGrothendieckFunctor :
    AddCommMonCat.{u} ⥤ AddCommGrpCat.{u} where
  obj M := AddCommGrpCat.of (Algebra.GrothendieckAddGroup (M : Type u))
  map f := AddCommGrpCat.ofHom (mathlibGrothendieckMap f.hom')
  map_id M := by
    apply AddCommGrpCat.hom_ext
    exact mathlibGrothendieckMap_id (M : Type u)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact mathlibGrothendieckMap_comp f.hom' g.hom'

noncomputable def grothendieckMathlibIso (M : AddCommMonCat.{u}) :
    InfoGeometry.Categorical.grothendieckCompletionFunctor.obj M ≅ mathlibGrothendieckFunctor.obj M where
  hom := AddCommGrpCat.ofHom
    (grothendieckMathlibEquiv (M := (M : Type u)).toAddMonoidHom)
  inv := AddCommGrpCat.ofHom
    (grothendieckMathlibEquiv (M := (M : Type u)).symm.toAddMonoidHom)
  hom_inv_id := by
    apply AddCommGrpCat.hom_ext
    ext x
    simp
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    ext x
    simp

noncomputable def grothendieckFunctorNatIso :
    InfoGeometry.Categorical.grothendieckCompletionFunctor ≅ mathlibGrothendieckFunctor :=
  NatIso.ofComponents grothendieckMathlibIso (by
    intro M N f
    apply AddCommGrpCat.hom_ext
    ext x
    exact _root_.grothendieckMathlibEquiv_naturality f.hom' x)

@[simp] theorem grothendieckFunctorNatIso_hom_app (M : AddCommMonCat.{u}) :
    (grothendieckFunctorNatIso.hom.app M).hom' =
      grothendieckMathlibEquiv (M := (M : Type u)).toAddMonoidHom := rfl

theorem grothendieckFunctorNatIso_naturality
    {M N : AddCommMonCat.{u}} (f : M ⟶ N) :
    InfoGeometry.Categorical.grothendieckCompletionFunctor.map f ≫ grothendieckFunctorNatIso.hom.app N =
      grothendieckFunctorNatIso.hom.app M ≫ mathlibGrothendieckFunctor.map f :=
  grothendieckFunctorNatIso.hom.naturality f

end InfoGeometry.Algebra.GrothendieckMathlibNatIso

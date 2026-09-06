import Mathlib
import InfoGeometry.Algebra.Grothendieck

/-!
# Categorical migration from the custom Grothendieck completion to Mathlib

This module upgrades the pointwise comparison between the repository's custom
Grothendieck group and Mathlib's `Algebra.GrothendieckAddGroup` to a natural
isomorphism of functors

`AddCommMonCat ⥤ AddCommGrpCat`.

The comparison is driven only by the two universal properties.  No quotient
representative unfolding is used in the naturality proof.
-/

noncomputable section

open CategoryTheory

namespace InfoGeometry.Algebra.GrothendieckMathlibNatIso

universe u

/-! ## Mathlib universal-property helpers -/

@[simp] theorem mathlibGrothendieckLift_of
    {M G : Type u} [AddCommMonoid M] [AddCommGroup G]
    (f : M →+ G) (m : M) :
    Algebra.GrothendieckAddGroup.lift f
        (Algebra.GrothendieckAddGroup.of m) = f m := by
  have h :
      (Algebra.GrothendieckAddGroup.lift f).comp
          Algebra.GrothendieckAddGroup.of = f := by
    rw [← Algebra.GrothendieckAddGroup.lift_symm_apply]
    exact Equiv.symm_apply_apply Algebra.GrothendieckAddGroup.lift f
  exact DFunLike.congr_fun h m

/-! ## Pointwise additive equivalence -/

noncomputable def grothendieckToMathlib
    (M : Type u) [AddCommMonoid M] :
    Grothendieck M →+ Algebra.GrothendieckAddGroup M :=
  grothendieckLift Algebra.GrothendieckAddGroup.of

noncomputable def mathlibToGrothendieck
    (M : Type u) [AddCommMonoid M] :
    Algebra.GrothendieckAddGroup M →+ Grothendieck M :=
  Algebra.GrothendieckAddGroup.lift (grothendieckMap M)

@[simp] theorem grothendieckToMathlib_map
    {M : Type u} [AddCommMonoid M] (m : M) :
    grothendieckToMathlib M (grothendieckMap M m) =
      Algebra.GrothendieckAddGroup.of m := by
  exact grothendieckLift_comp Algebra.GrothendieckAddGroup.of m

@[simp] theorem mathlibToGrothendieck_of
    {M : Type u} [AddCommMonoid M] (m : M) :
    mathlibToGrothendieck M (Algebra.GrothendieckAddGroup.of m) =
      grothendieckMap M m := by
  exact mathlibGrothendieckLift_of (grothendieckMap M) m

@[simp] theorem mathlibToGrothendieck_grothendieckToMathlib
    {M : Type u} [AddCommMonoid M] (x : Grothendieck M) :
    mathlibToGrothendieck M (grothendieckToMathlib M x) = x := by
  rcases grothendieck_eq_sub x with ⟨a, b, rfl⟩
  simp

@[simp] theorem grothendieckToMathlib_mathlibToGrothendieck
    {M : Type u} [AddCommMonoid M]
    (x : Algebra.GrothendieckAddGroup M) :
    grothendieckToMathlib M (mathlibToGrothendieck M x) = x := by
  let h : Algebra.GrothendieckAddGroup M →+
      Algebra.GrothendieckAddGroup M :=
    (grothendieckToMathlib M).comp (mathlibToGrothendieck M)
  have hh : h = AddMonoidHom.id (Algebra.GrothendieckAddGroup M) := by
    apply (Algebra.GrothendieckAddGroup.lift
      (M := M) (G := Algebra.GrothendieckAddGroup M)).symm.injective
    rw [Algebra.GrothendieckAddGroup.lift_symm_apply,
      Algebra.GrothendieckAddGroup.lift_symm_apply]
    ext m
    simp [h]
  exact DFunLike.congr_fun hh x

/-- The repository quotient model is canonically additively equivalent to
Mathlib's Grothendieck additive group. -/
noncomputable def grothendieckMathlibEquiv
    (M : Type u) [AddCommMonoid M] :
    Grothendieck M ≃+ Algebra.GrothendieckAddGroup M where
  toFun := grothendieckToMathlib M
  invFun := mathlibToGrothendieck M
  left_inv := mathlibToGrothendieck_grothendieckToMathlib
  right_inv := grothendieckToMathlib_mathlibToGrothendieck
  map_add' x y := (grothendieckToMathlib M).map_add x y

/-! ## The Mathlib-induced completion map -/

noncomputable def mathlibGrothendieckMap
    {M N : Type u} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) :
    Algebra.GrothendieckAddGroup M →+
      Algebra.GrothendieckAddGroup N :=
  Algebra.GrothendieckAddGroup.lift
    (Algebra.GrothendieckAddGroup.of.comp f)

@[simp] theorem mathlibGrothendieckMap_of
    {M N : Type u} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) (m : M) :
    mathlibGrothendieckMap f (Algebra.GrothendieckAddGroup.of m) =
      Algebra.GrothendieckAddGroup.of (f m) := by
  exact mathlibGrothendieckLift_of
    (Algebra.GrothendieckAddGroup.of.comp f) m

@[simp] theorem mathlibGrothendieckMap_id
    (M : Type u) [AddCommMonoid M] :
    mathlibGrothendieckMap (AddMonoidHom.id M) =
      AddMonoidHom.id (Algebra.GrothendieckAddGroup M) := by
  apply (Algebra.GrothendieckAddGroup.lift
    (M := M) (G := Algebra.GrothendieckAddGroup M)).symm.injective
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply,
    Algebra.GrothendieckAddGroup.lift_symm_apply]
  ext m
  simp

@[simp] theorem mathlibGrothendieckMap_comp
    {M N P : Type u}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    (f : M →+ N) (g : N →+ P) :
    mathlibGrothendieckMap (g.comp f) =
      (mathlibGrothendieckMap g).comp (mathlibGrothendieckMap f) := by
  apply (Algebra.GrothendieckAddGroup.lift
    (M := M) (G := Algebra.GrothendieckAddGroup P)).symm.injective
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply,
    Algebra.GrothendieckAddGroup.lift_symm_apply]
  ext m
  simp

/-! ## Completion functors -/

/-- The repository custom Grothendieck completion as a functor. -/
noncomputable def customGrothendieckFunctor :
    AddCommMonCat.{u} ⥤ AddCommGrpCat.{u} where
  obj M := AddCommGrpCat.of (Grothendieck M)
  map f := AddCommGrpCat.ofHom
    (grothendieckFunctor (AddCommMonCat.Hom.hom f))
  map_id M := by
    apply AddCommGrpCat.hom_ext
    simpa using (grothendieckFunctor_id (M := (M : Type u)))
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    simpa using grothendieckFunctor_comp
      (AddCommMonCat.Hom.hom f) (AddCommMonCat.Hom.hom g)

/-- Mathlib's Grothendieck additive completion as a functor. -/
noncomputable def mathlibGrothendieckFunctor :
    AddCommMonCat.{u} ⥤ AddCommGrpCat.{u} where
  obj M := AddCommGrpCat.of (Algebra.GrothendieckAddGroup M)
  map f := AddCommGrpCat.ofHom
    (mathlibGrothendieckMap (AddCommMonCat.Hom.hom f))
  map_id M := by
    apply AddCommGrpCat.hom_ext
    simpa using mathlibGrothendieckMap_id (M : Type u)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    simpa using mathlibGrothendieckMap_comp
      (AddCommMonCat.Hom.hom f) (AddCommMonCat.Hom.hom g)

/-! ## Pointwise naturality -/

theorem grothendieckMathlibEquiv_naturality
    {M N : Type u} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) :
    (grothendieckToMathlib N).comp (grothendieckFunctor f) =
      (mathlibGrothendieckMap f).comp (grothendieckToMathlib M) := by
  rw [← grothendieckLift_naturality f
    (Algebra.GrothendieckAddGroup.of :
      N →+ Algebra.GrothendieckAddGroup N)]
  ext x
  exact (grothendieckLift_unique
    ((Algebra.GrothendieckAddGroup.of :
      N →+ Algebra.GrothendieckAddGroup N).comp f)
    ((mathlibGrothendieckMap f).comp (grothendieckToMathlib M))
    (by
      intro m
      simp)
    x).symm

/-! ## The categorical natural isomorphism -/

noncomputable def grothendieckMathlibIso (M : AddCommMonCat.{u}) :
    customGrothendieckFunctor.obj M ≅ mathlibGrothendieckFunctor.obj M where
  hom := AddCommGrpCat.ofHom
    (grothendieckMathlibEquiv (M : Type u)).toAddMonoidHom
  inv := AddCommGrpCat.ofHom
    (grothendieckMathlibEquiv (M : Type u)).symm.toAddMonoidHom
  hom_inv_id := by
    apply AddCommGrpCat.hom_ext
    ext x
    simp
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    ext x
    simp

/-- Canonical natural isomorphism between the repository completion functor and
Mathlib's Grothendieck additive completion functor. -/
noncomputable def grothendieckFunctorNatIso :
    customGrothendieckFunctor ≅ mathlibGrothendieckFunctor :=
  NatIso.ofComponents grothendieckMathlibIso (by
    intro M N f
    apply AddCommGrpCat.hom_ext
    simpa [customGrothendieckFunctor, mathlibGrothendieckFunctor,
      grothendieckMathlibIso] using
      grothendieckMathlibEquiv_naturality
        (AddCommMonCat.Hom.hom f))

/-- The component of the natural isomorphism is exactly the pointwise additive
Grothendieck equivalence. -/
@[simp] theorem grothendieckFunctorNatIso_hom_app
    (M : AddCommMonCat.{u}) :
    AddCommGrpCat.Hom.hom (grothendieckFunctorNatIso.hom.app M) =
      (grothendieckMathlibEquiv (M : Type u)).toAddMonoidHom := by
  rfl

/-- The categorical commuting square for every additive commutative monoid
homomorphism. -/
theorem grothendieckFunctorNatIso_naturality
    {M N : AddCommMonCat.{u}} (f : M ⟶ N) :
    customGrothendieckFunctor.map f ≫
        grothendieckFunctorNatIso.hom.app N =
      grothendieckFunctorNatIso.hom.app M ≫
        mathlibGrothendieckFunctor.map f :=
  grothendieckFunctorNatIso.hom.naturality f

end InfoGeometry.Algebra.GrothendieckMathlibNatIso

end noncomputable section

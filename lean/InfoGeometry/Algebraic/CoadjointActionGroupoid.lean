/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SouriauContragredientPairing
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Contragredient action groupoids and fixed arrows

A bundled representation and an intertwining pair of automorphisms induce
an equivalence of the native action groupoid. The subgroup fixed by the group
automorphism acts on the submodule fixed by the contragredient symmetry.
Its action groupoid includes faithfully in the original one, with exactly
the fixed group labels between its fixed objects.

These are algebraic constructions. The representation is not asserted to
come from differentiation of a Lie group. No triality identification,
symplectic form, smooth fixed locus, or symplectic subgroupoid is inferred.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CoadjointActionGroupoid

open CategoryTheory
open InfoGeometry.Canonical.SouriauContragredientPairing

section ActionFunctor

variable {G H X Y : Type*} [Monoid G] [Monoid H]
  [MulAction G X] [MulAction H Y]

/-- A map of actions, allowing the acting monoid to change, induces a functor
between their native categories of elements. -/
def actionFunctor (φ : G →* H) (f : X → Y)
    (hf : ∀ g x, f (g • x) = φ g • f x) :
    ActionCategory G X ⥤ ActionCategory H Y where
  obj x := ActionCategory.objEquiv H Y (f x.back)
  map {x y} a := Functor.Elements.homMk (φ a.hom)
    ((hf a.hom x.back).symm.trans (congrArg f a.map_val))
  map_id x := by
    apply Functor.Elements.hom_ext
    exact φ.map_one
  map_comp a b := by
    apply Functor.Elements.hom_ext
    exact φ.map_mul b.hom a.hom

@[simp] theorem actionFunctor_obj_back (φ : G →* H) (f : X → Y)
    (hf : ∀ g x, f (g • x) = φ g • f x) (x : ActionCategory G X) :
    ((actionFunctor φ f hf).obj x).back = f x.back := rfl

@[simp] theorem actionFunctor_map_hom (φ : G →* H) (f : X → Y)
    (hf : ∀ g x, f (g • x) = φ g • f x)
    {x y : ActionCategory G X} (a : x ⟶ y) :
    ((actionFunctor φ f hf).map a).hom = φ a.hom := rfl

end ActionFunctor

section ActionEquivalence

variable {G X : Type*} [Group G] [MulAction G X]

/-- Equality of the represented points gives the identity-labelled native
isomorphism, without discarding the typed endpoints. -/
private def pointIso (x y : ActionCategory G X) (h : x.back = y.back) : x ≅ y where
  hom := Functor.Elements.homMk (1 : G) (by
    change (1 : G) • x.back = y.back
    simpa only [one_smul] using h)
  inv := Functor.Elements.homMk (1 : G) (by
    change (1 : G) • y.back = x.back
    simpa only [one_smul] using h.symm)
  hom_inv_id := by
    apply Functor.Elements.hom_ext
    exact one_mul (1 : G)
  inv_hom_id := by
    apply Functor.Elements.hom_ext
    exact one_mul (1 : G)

/-- A twisted equivariant equivalence gives an actual equivalence of native
action groupoids. Its inverse uses the inverse group and point maps. -/
def actionEquivalence (τ : G ≃* G) (σ : X ≃ X)
    (hσ : ∀ g x, σ (g • x) = τ g • σ x) :
    ActionCategory G X ≌ ActionCategory G X := by
  have hσinv : ∀ g x, σ.symm (g • x) = τ.symm g • σ.symm x := by
    intro g x
    apply σ.injective
    rw [σ.apply_symm_apply, hσ, τ.apply_symm_apply, σ.apply_symm_apply]
  let F := actionFunctor τ.toMonoidHom σ hσ
  let I := actionFunctor τ.symm.toMonoidHom σ.symm hσinv
  let η : 𝟭 (ActionCategory G X) ≅ F ⋙ I :=
    NatIso.ofComponents (fun x => pointIso _ _ (by
      change x.back = σ.symm (σ x.back)
      exact (σ.symm_apply_apply x.back).symm)) (by
      intro x y a
      apply Functor.Elements.hom_ext
      change (1 : G) * a.hom = τ.symm (τ a.hom) * 1
      simp)
  let ε : I ⋙ F ≅ 𝟭 (ActionCategory G X) :=
    NatIso.ofComponents (fun x => pointIso _ _ (by
      change σ (σ.symm x.back) = x.back
      exact σ.apply_symm_apply x.back)) (by
      intro x y a
      apply Functor.Elements.hom_ext
      change (1 : G) * τ (τ.symm a.hom) = a.hom * 1
      simp)
  exact CategoryTheory.Equivalence.mk F I η ε

@[simp] theorem actionEquivalence_obj_back (τ : G ≃* G) (σ : X ≃ X)
    (hσ : ∀ g x, σ (g • x) = τ g • σ x) (x : ActionCategory G X) :
    ((actionEquivalence τ σ hσ).functor.obj x).back = σ x.back := rfl

@[simp] theorem actionEquivalence_map_hom (τ : G ≃* G) (σ : X ≃ X)
    (hσ : ∀ g x, σ (g • x) = τ g • σ x)
    {x y : ActionCategory G X} (a : x ⟶ y) :
    ((actionEquivalence τ σ hσ).functor.map a).hom = τ a.hom := rfl

end ActionEquivalence

section Coadjoint

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]

/-- Compose the existing general-linear contragredient representation with
the supplied bundled representation. No action law is supplied separately. -/
def coadjointRepresentation (Ad : G →* (V ≃ₗ[ℝ] V)) :
    G →* (Module.Dual ℝ V ≃ₗ[ℝ] Module.Dual ℝ V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (Module.Dual ℝ V)).toMonoidHom.comp
    (contragredientGeneralLinearRepresentation.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ V).symm.toMonoidHom.comp Ad))

@[simp] theorem coadjointRepresentation_apply (Ad : G →* (V ≃ₗ[ℝ] V))
    (g : G) (μ : Module.Dual ℝ V) :
    coadjointRepresentation Ad g μ = contragredientLinearEquiv (Ad g) μ := rfl

@[simp] theorem coadjointRepresentation_apply_apply (Ad : G →* (V ≃ₗ[ℝ] V))
    (g : G) (μ : Module.Dual ℝ V) (x : V) :
    coadjointRepresentation Ad g μ x = μ ((Ad g).symm x) := rfl

/-- Pull back the native evaluation action of linear equivalences. -/
@[instance_reducible] def coadjointMulAction (Ad : G →* (V ≃ₗ[ℝ] V)) :
    MulAction G (Module.Dual ℝ V) :=
  MulAction.compHom _ (coadjointRepresentation Ad)

/-- The native action groupoid for the actual contragredient action. -/
abbrev CoadjointGroupoid (Ad : G →* (V ≃ₗ[ℝ] V)) :=
  @ActionCategory G _ (Module.Dual ℝ V) (coadjointMulAction Ad)

/-- The primal intertwining identity implies the dual intertwining identity;
the inverse in the dual pullback is essential. -/
theorem coadjoint_intertwines (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x))
    (g : G) (μ : Module.Dual ℝ V) :
    contragredientLinearEquiv A (coadjointRepresentation Ad g μ) =
      coadjointRepresentation Ad (τ g) (contragredientLinearEquiv A μ) := by
  ext x
  change μ ((Ad g).symm (A.symm x)) = μ (A.symm ((Ad (τ g)).symm x))
  apply congrArg μ
  apply A.injective
  apply (Ad (τ g)).injective
  rw [← hA g ((Ad g).symm (A.symm x))]
  simp only [LinearEquiv.apply_symm_apply]

/-- The intertwining pair acts by a genuine equivalence of the native
coadjoint action groupoid, with object map the existing contragredient map. -/
def coadjointActionEquivalence (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x)) :
    CoadjointGroupoid Ad ≌ CoadjointGroupoid Ad := by
  letI := coadjointMulAction Ad
  exact actionEquivalence τ (contragredientLinearEquiv A).toEquiv
    (coadjoint_intertwines Ad τ A hA)

/-- Native equalizer subgroup of the group automorphism and the identity. -/
def fixedSubgroup (τ : G ≃* G) : Subgroup G :=
  τ.toMonoidHom.eqLocus (MonoidHom.id G)

@[simp] theorem mem_fixedSubgroup (τ : G ≃* G) (g : G) :
    g ∈ fixedSubgroup τ ↔ τ g = g := Iff.rfl

/-- The actual dual submodule fixed by pullback along the inverse symmetry. -/
def fixedDualSubmodule (A : V ≃ₗ[ℝ] V) : Submodule ℝ (Module.Dual ℝ V) :=
  (contragredient A).fixedSubmodule

@[simp] theorem mem_fixedDualSubmodule (A : V ≃ₗ[ℝ] V) (μ : Module.Dual ℝ V) :
    μ ∈ fixedDualSubmodule A ↔ contragredientLinearEquiv A μ = μ := Iff.rfl

/-- Closure of the fixed dual submodule is derived from intertwining and
fixedness of the acting group element. -/
theorem coadjoint_mem_fixedDualSubmodule (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x))
    {g : G} (hg : g ∈ fixedSubgroup τ)
    {μ : Module.Dual ℝ V} (hμ : μ ∈ fixedDualSubmodule A) :
    coadjointRepresentation Ad g μ ∈ fixedDualSubmodule A := by
  change τ g = g at hg
  change contragredientLinearEquiv A μ = μ at hμ
  change contragredientLinearEquiv A (coadjointRepresentation Ad g μ) =
    coadjointRepresentation Ad g μ
  rw [coadjoint_intertwines Ad τ A hA, hg, hμ]

/-- The fixed subgroup acts on the fixed dual submodule by restriction of
the existing contragredient action. -/
@[instance_reducible] def fixedDualMulAction (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x)) :
    MulAction (fixedSubgroup τ) (fixedDualSubmodule A) where
  smul g μ := ⟨coadjointRepresentation Ad (g : G) (μ : Module.Dual ℝ V),
    coadjoint_mem_fixedDualSubmodule Ad τ A hA g.property μ.property⟩
  one_smul μ := by
    apply Subtype.ext
    change coadjointRepresentation Ad (1 : G) (μ : Module.Dual ℝ V) = μ
    rw [map_one]
    rfl
  mul_smul g h μ := by
    apply Subtype.ext
    change coadjointRepresentation Ad ((g : G) * (h : G)) (μ : Module.Dual ℝ V) =
      coadjointRepresentation Ad (g : G)
        (coadjointRepresentation Ad (h : G) (μ : Module.Dual ℝ V))
    rw [map_mul]
    rfl

/-- Its native action category carries Mathlib's groupoid instance. -/
abbrev FixedCoadjointGroupoid (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x)) :=
  @ActionCategory (fixedSubgroup τ) _ (fixedDualSubmodule A)
    (fixedDualMulAction Ad τ A hA)

/-- Inclusion retains both the fixed dual point and the fixed group label. -/
def fixedActionInclusion (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x)) :
    FixedCoadjointGroupoid Ad τ A hA ⥤ CoadjointGroupoid Ad := by
  letI := coadjointMulAction Ad
  letI := fixedDualMulAction Ad τ A hA
  exact actionFunctor (fixedSubgroup τ).subtype
    (fun μ : fixedDualSubmodule A => (μ : Module.Dual ℝ V)) (fun _ _ => rfl)

instance fixedActionInclusion_faithful (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x)) :
    (fixedActionInclusion Ad τ A hA).Faithful where
  map_injective {x y} f g h := by
    apply Functor.Elements.hom_ext
    apply Subtype.ext
    exact congrArg (fun a => a.hom) h

/-- Fixed-groupoid arrows correspond exactly to ambient arrows whose group
labels are fixed, with both endpoints already in the fixed dual submodule. -/
def fixedArrowEquiv (Ad : G →* (V ≃ₗ[ℝ] V)) (τ : G ≃* G)
    (A : V ≃ₗ[ℝ] V)
    (hA : ∀ g x, A (Ad g x) = Ad (τ g) (A x))
    (x y : FixedCoadjointGroupoid Ad τ A hA) :
    (x ⟶ y) ≃
      {f : (fixedActionInclusion Ad τ A hA).obj x ⟶
        (fixedActionInclusion Ad τ A hA).obj y // τ f.hom = f.hom} where
  toFun f := ⟨(fixedActionInclusion Ad τ A hA).map f, f.hom.property⟩
  invFun f := Functor.Elements.homMk ⟨f.val.hom, f.property⟩ (by
    apply Subtype.ext
    exact f.val.map_val)
  left_inv f := by
    apply Functor.Elements.hom_ext
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Functor.Elements.hom_ext
    rfl

end Coadjoint

end InfoGeometry.Algebraic.CoadjointActionGroupoid

end

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauContragredientPairing
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Contragredient action groupoids and equivariant automorphisms

The underlying group action is a native monoid homomorphism into linear
equivalences. Its contragredient action gives Mathlib's `ActionCategory`,
including its native `Groupoid` instance. A raw arrow is `(k, α)`, with source
`α` and target `α ∘ Ad(k⁻¹)`. The product of raw arrows is only exposed with
the composability equation `source x = target y`.

The fixed construction is the action groupoid of the fixed subgroup on the
fixed dual submodule. This is an algebraic groupoid; no smooth manifold,
cotangent bundle identification, or nondegenerate fixed symplectic form is
asserted by this file.
-/

noncomputable section

namespace InfoGeometry.Geometry.CotangentActionGroupoid

open CategoryTheory
open InfoGeometry.Canonical.SouriauContragredientPairing

variable {R G V : Type*} [CommSemiring R] [Group G] [AddCommMonoid V] [Module R V]

/-- The contragredient of a specified representation. -/
def coadj (Ad : G →* (V ≃ₗ[R] V)) (k : G) :
    Module.Dual R V →ₗ[R] Module.Dual R V :=
  contragredient (Ad k)

@[simp] theorem coadj_apply (Ad : G →* (V ≃ₗ[R] V)) (k : G)
    (α : Module.Dual R V) (v : V) :
    coadj Ad k α v = α (Ad k⁻¹ v) := by
  change α ((Ad k).symm v) = α (Ad k⁻¹ v)
  rw [map_inv]
  rfl

@[simp] theorem coadj_one (Ad : G →* (V ≃ₗ[R] V)) (α : Module.Dual R V) :
    coadj Ad 1 α = α := by
  ext v
  simp

theorem coadj_mul (Ad : G →* (V ≃ₗ[R] V)) (k l : G) (α : Module.Dual R V) :
    coadj Ad (k * l) α = coadj Ad k (coadj Ad l α) := by
  ext v
  simp [mul_inv_rev, map_mul, LinearEquiv.mul_apply]

@[simp] theorem coadj_inv_coadj (Ad : G →* (V ≃ₗ[R] V))
    (k : G) (α : Module.Dual R V) :
    coadj Ad k⁻¹ (coadj Ad k α) = α := by
  rw [← coadj_mul, inv_mul_cancel, coadj_one]

@[simp] theorem coadj_coadj_inv (Ad : G →* (V ≃ₗ[R] V))
    (k : G) (α : Module.Dual R V) :
    coadj Ad k (coadj Ad k⁻¹ α) = α := by
  rw [← coadj_mul, mul_inv_cancel, coadj_one]

/-- The genuine group action required by Mathlib's action groupoid. -/
def coadjointAction (Ad : G →* (V ≃ₗ[R] V)) : MulAction G (Module.Dual R V) where
  smul := fun k α => coadj Ad k α
  one_smul := coadj_one Ad
  mul_smul := coadj_mul Ad

/-- The native algebraic groupoid of the contragredient action. -/
abbrev CotangentGroupoid (Ad : G →* (V ≃ₗ[R] V)) :=
  letI := coadjointAction Ad
  ActionCategory G (Module.Dual R V)

instance cotangentGroupoid (Ad : G →* (V ≃ₗ[R] V)) : Groupoid (CotangentGroupoid Ad) := by
  letI := coadjointAction Ad
  exact inferInstanceAs (Groupoid (ActionCategory G (Module.Dual R V)))

/-- Source-trivialized arrows, before selecting their endpoints. -/
abbrev Arrow (G V : Type*) [AddCommMonoid V] [Module R V] := G × Module.Dual R V

def source (x : Arrow (R := R) G V) : Module.Dual R V := x.2

def target (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    Module.Dual R V := coadj Ad x.1 x.2

def unit (α : Module.Dual R V) : Arrow (R := R) G V := (1, α)

def inverse (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    Arrow (R := R) G V := (x.1⁻¹, target Ad x)

/-- `x` follows `y`; hence the categorical order is `y ≫ x`. -/
def Composable (Ad : G →* (V ≃ₗ[R] V)) (x y : Arrow (R := R) G V) : Prop :=
  source x = target Ad y

/-- Multiplication is exposed only for composable arrows. -/
def comp (Ad : G →* (V ≃ₗ[R] V)) (x y : Arrow (R := R) G V)
    (_h : Composable Ad x y) : Arrow (R := R) G V := (x.1 * y.1, y.2)

@[simp] theorem source_unit (α : Module.Dual R V) : source (unit (G := G) α) = α := rfl

@[simp] theorem target_unit (Ad : G →* (V ≃ₗ[R] V)) (α : Module.Dual R V) :
    target Ad (unit α) = α := coadj_one Ad α

@[simp] theorem source_inverse (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    source (inverse Ad x) = target Ad x := rfl

@[simp] theorem target_inverse (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    target Ad (inverse Ad x) = source x := by
  exact coadj_inv_coadj Ad x.1 x.2

@[simp] theorem inverse_inverse (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    inverse Ad (inverse Ad x) = x := by
  apply Prod.ext
  · simp [inverse]
  · exact target_inverse Ad x

@[simp] theorem source_comp (Ad : G →* (V ≃ₗ[R] V))
    (x y : Arrow (R := R) G V) (h : Composable Ad x y) :
    source (comp Ad x y h) = source y := rfl

@[simp] theorem target_comp (Ad : G →* (V ≃ₗ[R] V))
    (x y : Arrow (R := R) G V) (h : Composable Ad x y) :
    target Ad (comp Ad x y h) = target Ad x := by
  change coadj Ad (x.1 * y.1) y.2 = coadj Ad x.1 x.2
  rw [coadj_mul]
  exact congrArg (coadj Ad x.1) h.symm

theorem unit_comp (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    comp Ad (unit (target Ad x)) x rfl = x := by
  apply Prod.ext <;> simp [comp, unit]

theorem comp_unit (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    comp Ad x (unit (source x)) (by simp [Composable]) = x := by
  apply Prod.ext <;> simp [comp, unit, source]

theorem inverse_comp (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    comp Ad (inverse Ad x) x rfl = unit (source x) := by
  apply Prod.ext <;> simp [comp, inverse, unit, source]

theorem comp_inverse (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    comp Ad x (inverse Ad x) (by simp [Composable]) = unit (target Ad x) := by
  apply Prod.ext <;> simp [comp, inverse, unit]

theorem comp_assoc (Ad : G →* (V ≃ₗ[R] V)) (x y z : Arrow (R := R) G V)
    (hxy : Composable Ad x y) (hyz : Composable Ad y z) :
    comp Ad (comp Ad x y hxy) z (by simpa [Composable] using hyz) =
      comp Ad x (comp Ad y z hyz) (by simpa [Composable] using hxy) := by
  apply Prod.ext
  · exact mul_assoc x.1 y.1 z.1
  · rfl

/-- The dual point as an object of the native groupoid. -/
def object (Ad : G →* (V ≃ₗ[R] V)) (α : Module.Dual R V) : CotangentGroupoid Ad :=
  letI := coadjointAction Ad
  (ActionCategory.objEquiv G (Module.Dual R V)) α

/-- Every source-trivialized arrow gives a morphism with its actual endpoints. -/
def toHom (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    object Ad (source x) ⟶ object Ad (target Ad x) :=
  letI := coadjointAction Ad
  Functor.Elements.homMk x.1 rfl

/-- A native morphism determines its source-trivialized arrow. -/
def fromHom (Ad : G →* (V ≃ₗ[R] V))
    {α β : CotangentGroupoid Ad} (f : α ⟶ β) : Arrow (R := R) G V :=
  (f.hom, α.val)

@[simp] theorem target_fromHom (Ad : G →* (V ≃ₗ[R] V))
    {α β : CotangentGroupoid Ad} (f : α ⟶ β) :
    target Ad (fromHom Ad f) = β.val := f.map_val

@[simp] theorem fromHom_toHom (Ad : G →* (V ≃ₗ[R] V)) (x : Arrow (R := R) G V) :
    fromHom Ad (toHom Ad x) = x := rfl

/-- The group label of native composition has the required reversed order. -/
theorem toHom_comp_label (Ad : G →* (V ≃ₗ[R] V))
    {α β γ : CotangentGroupoid Ad} (f : α ⟶ β) (h : β ⟶ γ) :
    (f ≫ h).hom = h.hom * f.hom := rfl

/-- Native composition is exactly the composability-restricted raw multiplication. -/
theorem fromHom_comp (Ad : G →* (V ≃ₗ[R] V))
    {α β γ : CotangentGroupoid Ad} (f : α ⟶ β) (h : β ⟶ γ) :
    fromHom Ad (f ≫ h) = comp Ad (fromHom Ad h) (fromHom Ad f)
      (by exact f.map_val.symm) := rfl

/-- Equivariance of the coadjoint action is derived from equivariance on vectors. -/
theorem coadj_intertwine (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    (k : G) (α : Module.Dual R V) :
    coadj Ad (τ k) (contragredient dτ α) =
      contragredient dτ (coadj Ad k α) := by
  ext v
  change α (dτ.symm ((Ad (τ k)).symm v)) = α ((Ad k).symm (dτ.symm v))
  congr 1
  apply dτ.injective
  rw [dτ.apply_symm_apply]
  apply (Ad (τ k)).injective
  rw [LinearEquiv.apply_symm_apply, ← hAd]
  simp

/-- The lifted arrow map is an actual equivalence. -/
def lift (τ : G ≃* G) (dτ : V ≃ₗ[R] V) :
    Arrow (R := R) G V ≃ Arrow (R := R) G V :=
  τ.toEquiv.prodCongr (contragredientLinearEquiv dτ).toEquiv

/-- Fixed arrows are precisely fixed group elements paired with fixed covectors. -/
theorem lift_fixed_iff (τ : G ≃* G) (dτ : V ≃ₗ[R] V) (x : Arrow (R := R) G V) :
    lift τ dτ x = x ↔ τ x.1 = x.1 ∧ contragredient dτ x.2 = x.2 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hg, hα⟩
    exact Prod.ext hg hα

@[simp] theorem source_lift (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (x : Arrow (R := R) G V) :
    source (lift τ dτ x) = contragredient dτ (source x) := rfl

theorem target_lift (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    (x : Arrow (R := R) G V) :
    target Ad (lift τ dτ x) = contragredient dτ (target Ad x) :=
  coadj_intertwine Ad τ dτ hAd x.1 x.2

theorem composable_lift (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    {x y : Arrow (R := R) G V} (h : Composable Ad x y) :
    Composable Ad (lift τ dτ x) (lift τ dτ y) := by
  rw [Composable, source_lift, target_lift Ad τ dτ hAd, h]

@[simp] theorem lift_unit (τ : G ≃* G) (dτ : V ≃ₗ[R] V) (α : Module.Dual R V) :
    lift τ dτ (unit α) = unit (contragredient dτ α) := by
  apply Prod.ext
  · exact τ.map_one
  · rfl

theorem lift_inverse (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    (x : Arrow (R := R) G V) :
    lift τ dτ (inverse Ad x) = inverse Ad (lift τ dτ x) := by
  apply Prod.ext
  · exact map_inv τ x.1
  · exact (target_lift Ad τ dτ hAd x).symm

theorem lift_comp (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    (x y : Arrow (R := R) G V) (h : Composable Ad x y) :
    lift τ dτ (comp Ad x y h) =
      comp Ad (lift τ dτ x) (lift τ dτ y) (composable_lift Ad τ dτ hAd h) := by
  apply Prod.ext
  · exact τ.map_mul x.1 y.1
  · rfl

/-- The lift on the native action groupoid, with source and target enforced by types. -/
def liftFunctor (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    CotangentGroupoid Ad ⥤ CotangentGroupoid Ad := by
  letI := coadjointAction Ad
  exact
    { obj := fun α => object Ad (contragredient dτ α.val)
      map := fun {α β} f => Functor.Elements.homMk (τ f.hom) (by
        change coadj Ad (τ f.hom) (contragredient dτ α.val) = contragredient dτ β.val
        rw [coadj_intertwine Ad τ dτ hAd]
        exact congrArg (contragredient dτ) f.map_val)
      map_id := fun α => by
        apply Functor.Elements.hom_ext
        exact τ.map_one
      map_comp := fun f h => by
        apply Functor.Elements.hom_ext
        exact τ.map_mul h.hom f.hom }

instance liftFunctor_faithful (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    (liftFunctor Ad τ dτ hAd).Faithful where
  map_injective h := by
    apply Functor.Elements.hom_ext
    apply τ.injective
    exact congrArg (fun f => f.hom) h

instance liftFunctor_full (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    (liftFunctor Ad τ dτ hAd).Full where
  map_surjective {α β} f := by
    refine ⟨Functor.Elements.homMk (τ.symm f.hom) ?_, ?_⟩
    · apply (contragredientLinearEquiv dτ).injective
      change contragredient dτ (coadj Ad (τ.symm f.hom) α.val) =
        contragredient dτ β.val
      rw [← coadj_intertwine Ad τ dτ hAd, τ.apply_symm_apply]
      exact f.map_val
    · apply Functor.Elements.hom_ext
      exact τ.apply_symm_apply f.hom

instance liftFunctor_essSurj (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    (liftFunctor Ad τ dτ hAd).EssSurj := by
  apply Functor.essSurj_of_surj
  intro α
  refine ⟨object Ad (contragredient dτ.symm α.val), ?_⟩
  change object Ad (contragredient dτ (contragredient dτ.symm α.val)) = α
  rw [contragredient_symm_right]
  exact ActionCategory.back_coe α

instance liftFunctor_isEquivalence (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    (liftFunctor Ad τ dτ hAd).IsEquivalence where

/-- A native equivalence of groupoids induced by the automorphism pair. -/
def liftEquivalence (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    CotangentGroupoid Ad ≌ CotangentGroupoid Ad :=
  (liftFunctor Ad τ dτ hAd).asEquivalence

/-- Fixed arrows have fixed source and fixed target, including the missing target closure. -/
theorem fixed_endpoints (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    (x : Arrow (R := R) G V) (hx : lift τ dτ x = x) :
    contragredient dτ (source x) = source x ∧
      contragredient dτ (target Ad x) = target Ad x := by
  constructor
  · exact congrArg source hx
  · rw [← target_lift Ad τ dτ hAd, hx]

theorem fixed_unit (τ : G ≃* G) (dτ : V ≃ₗ[R] V) (α : Module.Dual R V)
    (hα : contragredient dτ α = α) : lift τ dτ (unit α) = unit α := by
  rw [lift_unit, hα]

theorem fixed_inverse (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    (x : Arrow (R := R) G V) (hx : lift τ dτ x = x) :
    lift τ dτ (inverse Ad x) = inverse Ad x := by
  rw [lift_inverse Ad τ dτ hAd, hx]

theorem fixed_comp (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    (x y : Arrow (R := R) G V) (h : Composable Ad x y)
    (hx : lift τ dτ x = x) (hy : lift τ dτ y = y) :
    lift τ dτ (comp Ad x y h) = comp Ad x y h := by
  have hp := lift_comp Ad τ dτ hAd x y h
  simpa only [hx, hy] using hp

/-- The native equalizer subgroup of the group automorphism and the identity. -/
def fixedSubgroup (τ : G ≃* G) : Subgroup G :=
  τ.toMonoidHom.eqLocus (MonoidHom.id G)

/-- The native fixed submodule for the dual automorphism. -/
def fixedDual (dτ : V ≃ₗ[R] V) : Submodule R (Module.Dual R V) :=
  (contragredient dτ).fixedSubmodule

/-- The fixed subgroup acts on the fixed dual submodule. -/
def fixedAction (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    MulAction (fixedSubgroup τ) (fixedDual dτ) where
  smul k α := ⟨coadj Ad k.1 α.1, by
    change contragredient dτ (coadj Ad k.1 α.1) = coadj Ad k.1 α.1
    rw [← coadj_intertwine Ad τ dτ hAd, k.property, α.property]⟩
  one_smul α := by
    apply Subtype.ext
    exact coadj_one Ad α.1
  mul_smul k l α := by
    apply Subtype.ext
    exact coadj_mul Ad k.1 l.1 α.1

/-- The native groupoid of fixed objects and fixed arrows. -/
abbrev FixedGroupoid (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :=
  letI := fixedAction Ad τ dτ hAd
  ActionCategory (fixedSubgroup τ) (fixedDual dτ)

instance fixedGroupoid (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    Groupoid (FixedGroupoid Ad τ dτ hAd) := by
  letI := fixedAction Ad τ dτ hAd
  exact inferInstanceAs (Groupoid (ActionCategory (fixedSubgroup τ) (fixedDual dτ)))

/-- Inclusion remembers the underlying dual point and group element. -/
def fixedInclusion (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    FixedGroupoid Ad τ dτ hAd ⥤ CotangentGroupoid Ad := by
  letI := coadjointAction Ad
  letI := fixedAction Ad τ dτ hAd
  exact
    { obj := fun α => object Ad α.val.1
      map := fun f => Functor.Elements.homMk f.hom.1 (congrArg Subtype.val f.map_val)
      map_id := fun α => rfl
      map_comp := fun f h => rfl }

/-- The fixed groupoid embeds its objects as the actual fixed covectors. -/
theorem fixedInclusion_obj_injective (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    Function.Injective (fixedInclusion Ad τ dτ hAd).obj := by
  letI := fixedAction Ad τ dτ hAd
  intro α β h
  apply (ActionCategory.objEquiv (fixedSubgroup τ) (fixedDual dτ)).symm.injective
  apply Subtype.ext
  exact congrArg (fun x : CotangentGroupoid Ad => x.val) h

instance fixedInclusion_faithful (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v)) :
    (fixedInclusion Ad τ dτ hAd).Faithful where
  map_injective h := by
    apply Functor.Elements.hom_ext
    apply Subtype.ext
    exact congrArg (fun f => f.hom) h

/-- Every arrow of the fixed groupoid maps to a fixed ambient arrow. -/
theorem fixedInclusion_arrow_fixed (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    {α β : FixedGroupoid Ad τ dτ hAd} (f : α ⟶ β) :
    lift τ dτ (fromHom Ad ((fixedInclusion Ad τ dτ hAd).map f)) =
      fromHom Ad ((fixedInclusion Ad τ dτ hAd).map f) := by
  apply (lift_fixed_iff τ dτ _).mpr
  exact ⟨f.hom.property, α.val.property⟩

/-- Between fixed objects, precisely the fixed group labels come from the fixed groupoid.
The inclusion is therefore not asserted to be full. -/
theorem fixedInclusion_hom_range_iff (Ad : G →* (V ≃ₗ[R] V))
    (τ : G ≃* G) (dτ : V ≃ₗ[R] V)
    (hAd : ∀ k v, dτ (Ad k v) = Ad (τ k) (dτ v))
    {α β : FixedGroupoid Ad τ dτ hAd}
    (f : (fixedInclusion Ad τ dτ hAd).obj α ⟶ (fixedInclusion Ad τ dτ hAd).obj β) :
    (∃ h : α ⟶ β, (fixedInclusion Ad τ dτ hAd).map h = f) ↔ τ f.hom = f.hom := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.hom.property
  · intro hk
    refine ⟨Functor.Elements.homMk ⟨f.hom, hk⟩ (Subtype.ext f.map_val), ?_⟩
    apply Functor.Elements.hom_ext
    rfl

end InfoGeometry.Geometry.CotangentActionGroupoid

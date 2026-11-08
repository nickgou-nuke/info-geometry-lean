/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.CategoryTheory.Action.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Morita.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Tactic.FinCases

noncomputable section
open CategoryTheory
namespace InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita
abbrev C2 := Multiplicative (ZMod 2)
def generator : C2 := Multiplicative.ofAdd 1

theorem generator_sq : generator * generator = 1 := by
  change Multiplicative.ofAdd ((1 : ZMod 2) + 1) = Multiplicative.ofAdd 0
  congr 1

variable {A : Type*} [Ring A]

def involution (X : Action (ModuleCat A) C2) : X.V →ₗ[A] X.V :=
  (X.ρ generator).hom

theorem involution_sq (X : Action (ModuleCat A) C2) (x : X.V) :
    involution X (involution X x) = x := by
  have h : X.ρ generator ≫ X.ρ generator = 𝟙 X.V := by
    change X.ρ generator * X.ρ generator = _
    rw [← map_mul, generator_sq, map_one]
    rfl
  exact congrArg (fun f : X.V ⟶ X.V => f x) h

def grading (g : A) (X : Action (ModuleCat A) C2) (x : X.V) : X.V :=
  g • involution X x

theorem grading_sq (g : A) (hg : g * g = 1) (X : Action (ModuleCat A) C2) (x : X.V) :
    grading g X (grading g X x) = x := by
  simp only [grading, map_smul, involution_sq, smul_smul, hg, one_smul]

theorem grading_smul (g : A) (hg : g * g = 1) (X : Action (ModuleCat A) C2)
    (a : A) (x : X.V) : grading g X (a • x) = (g * a * g) • grading g X x := by
  simp [grading, smul_smul, mul_assoc, hg]

theorem morphism_even (g : A) {X Y : Action (ModuleCat A) C2} (f : X ⟶ Y) (x : X.V) :
    f.hom (grading g X x) = grading g Y (f.hom x) := by
  have h := congrArg (fun k : X.V ⟶ Y.V => k x) (f.comm generator)
  change f.hom (involution X x) = involution Y (f.hom x) at h
  simpa [grading] using congrArg (fun y : Y.V => g • y) h

theorem c2_cases (k : C2) : k = 1 ∨ k = generator := by
  fin_cases k <;> decide

theorem generator_ne_one : generator ≠ 1 := by decide

def actionOfInvolution (M : ModuleCat A) (j : M →ₗ[A] M)
    (hj : ∀ x, j (j x) = x) : Action (ModuleCat A) C2 where
  V := M
  ρ :=
    { toFun := fun k => if k = 1 then 1 else ModuleCat.ofHom j
      map_one' := by simp
      map_mul' := by
        intro k l
        rcases c2_cases k with rfl | rfl <;>
          rcases c2_cases l with rfl | rfl
        all_goals simp [generator_sq, generator_ne_one]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (hj x).symm }

theorem actionOfInvolution_generator (M : ModuleCat A) (j : M →ₗ[A] M)
    (hj : ∀ x, j (j x) = x) :
    involution (actionOfInvolution M j hj) = j := by
  change (if generator = 1 then (1 : End M) else ModuleCat.ofHom j).hom = j
  simp [generator_ne_one]

theorem morphism_even_iff (g : A) (hg : g * g = 1)
    {X Y : Action (ModuleCat A) C2} (f : X.V ⟶ Y.V) :
    (∀ x, f (grading g X x) = grading g Y (f x)) ↔
      ∀ k, X.ρ k ≫ f = f ≫ Y.ρ k := by
  constructor
  · intro h k
    rcases c2_cases k with rfl | rfl
    · simp
    · ext x
      change f (involution X x) = involution Y (f x)
      have hh := congrArg (fun y : Y.V => g • y) (h x)
      simpa [grading, smul_smul, hg] using hh
  · intro h x
    exact morphism_even g (⟨f, h⟩ : X ⟶ Y) x

def untwist (g : A) (hg : g * g = 1) (M : ModuleCat A) (γ : M →+ M)
    (hγ : ∀ a x, γ (a • x) = (g * a * g) • γ x) : M →ₗ[A] M where
  toFun x := g • γ x
  map_add' x y := by simp
  map_smul' a x := by simp [hγ, smul_smul, ← mul_assoc, hg]

theorem untwist_sq (g : A) (hg : g * g = 1) (M : ModuleCat A) (γ : M →+ M)
    (hγ : ∀ a x, γ (a • x) = (g * a * g) • γ x)
    (hγsq : ∀ x, γ (γ x) = x) (x : M) :
    untwist g hg M γ hγ (untwist g hg M γ hγ x) = x := by
  change g • γ (g • γ x) = x
  rw [hγ, hγsq]
  simp [hg, smul_smul]

/-- Every inner-semilinear grading determines an object of the native action category. -/
def actionOfGrading (g : A) (hg : g * g = 1) (M : ModuleCat A) (γ : M →+ M)
    (hγ : ∀ a x, γ (a • x) = (g * a * g) • γ x)
    (hγsq : ∀ x, γ (γ x) = x) : Action (ModuleCat A) C2 :=
  actionOfInvolution M (untwist g hg M γ hγ) (untwist_sq g hg M γ hγ hγsq)

theorem grading_reconstruct (g : A) (hg : g * g = 1) (M : ModuleCat A) (γ : M →+ M)
    (hγ : ∀ a x, γ (a • x) = (g * a * g) • γ x)
    (hγsq : ∀ x, γ (γ x) = x) (x : M) :
    grading g (actionOfGrading g hg M γ hγ hγsq) x = γ x := by
  unfold grading actionOfGrading
  rw [actionOfInvolution_generator]
  change g • (g • γ x) = γ x
  rw [smul_smul, hg, one_smul]

variable {B : Type*} [Ring B]

/-- Morita functors lift to inner-graded modules via their untwisted C₂ actions. -/
def gradedEquivalence (E : ModuleCat A ≌ ModuleCat B) :
    Action (ModuleCat A) C2 ≌ Action (ModuleCat B) C2 := E.mapAction C2

/-- A native Mathlib Morita equivalence induces an equivalence of the corresponding
`C₂`-action categories. This is the categorical graded lift; a bimodule
realization is additional data and is not part of Mathlib's `MoritaEquivalence`
structure. -/
def gradedMoritaEquivalence (E : MoritaEquivalence ℤ A B) :
    Action (ModuleCat A) C2 ≌ Action (ModuleCat B) C2 :=
  gradedEquivalence E.eqv

theorem functor_even (E : ModuleCat A ≌ ModuleCat B) (h : B)
    {X Y : Action (ModuleCat A) C2} (f : X ⟶ Y) (x : ((gradedEquivalence E).functor.obj X).V) :
    ((gradedEquivalence E).functor.map f).hom (grading h _ x) =
      grading h _ (((gradedEquivalence E).functor.map f).hom x) :=
  morphism_even h _ x

theorem inverse_even (E : ModuleCat A ≌ ModuleCat B) (g : A)
    {X Y : Action (ModuleCat B) C2} (f : X ⟶ Y) (x : ((gradedEquivalence E).inverse.obj X).V) :
    ((gradedEquivalence E).inverse.map f).hom (grading g _ x) =
      grading g _ (((gradedEquivalence E).inverse.map f).hom x) :=
  morphism_even g _ x

theorem unit_even (E : ModuleCat A ≌ ModuleCat B) (g : A)
    (X : Action (ModuleCat A) C2) (x : X.V) :
    ((gradedEquivalence E).unitIso.hom.app X).hom (grading g X x) =
      grading g _ (((gradedEquivalence E).unitIso.hom.app X).hom x) :=
  morphism_even g _ x

theorem counit_even (E : ModuleCat A ≌ ModuleCat B) (h : B)
    (Y : Action (ModuleCat B) C2)
    (y : ((gradedEquivalence E).functor.obj ((gradedEquivalence E).inverse.obj Y)).V) :
    ((gradedEquivalence E).counitIso.hom.app Y).hom (grading h _ y) =
      grading h Y (((gradedEquivalence E).counitIso.hom.app Y).hom y) :=
  morphism_even h _ y

/-- The unit of the lifted native Morita equivalence preserves the induced
inner grading. -/
theorem morita_unit_even (E : MoritaEquivalence ℤ A B) (g : A)
    (X : Action (ModuleCat A) C2) (x : X.V) :
    ((gradedMoritaEquivalence E).unitIso.hom.app X).hom (grading g X x) =
      grading g _ (((gradedMoritaEquivalence E).unitIso.hom.app X).hom x) :=
  unit_even E.eqv g X x

/-- The counit of the lifted native Morita equivalence preserves the induced
inner grading. -/
theorem morita_counit_even (E : MoritaEquivalence ℤ A B) (h : B)
    (Y : Action (ModuleCat B) C2)
    (y : ((gradedMoritaEquivalence E).functor.obj
      ((gradedMoritaEquivalence E).inverse.obj Y)).V) :
    ((gradedMoritaEquivalence E).counitIso.hom.app Y).hom (grading h _ y) =
      grading h Y (((gradedMoritaEquivalence E).counitIso.hom.app Y).hom y) :=
  counit_even E.eqv h Y y

end InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita

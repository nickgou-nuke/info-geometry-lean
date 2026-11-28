/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FlowErlangenClosure
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Basic.Real.Basic

/-!
# Automorphism closure for real functionals and bilinear forms

The full algebra-automorphism group of an associative real algebra acts on
linear functionals and bilinear forms by inverse pullback. The algebra need
not be commutative. Fixing a functional and a form is the stabilizer of their
pair in the native product action. The existing action-level Erlangen closure
therefore gives a genuine Galois-closure bound for automorphism-flow families.

A linear functional is not assumed to be a positive normalized state, and a
bilinear form is not assumed symmetric, nondegenerate, or positive. Such
properties belong to a specialization. No exponential, integration theorem,
complete positivity, or modular-flow identification is asserted here.

The two actions are selected with `open scoped OperatorInvariantPullback`.
Their explicit scoped scalar-action projections ensure that a form is pulled
back in both arguments, rather than only in its output linear-map argument.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure

open InfoGeometry.Canonical.FlowErlangenClosure

variable (A : Type*) [Ring A] [Algebra ℝ A]

/-- Inverse pullback of a real linear functional by an algebra automorphism. -/
abbrev algebraAutFunctionalAction : MulAction (A ≃ₐ[ℝ] A) (A →ₗ[ℝ] ℝ) where
  smul α ω := ω.comp α.symm.toLinearMap
  one_smul ω := by
    ext x
    rfl
  mul_smul α β ω := by
    ext x
    rfl

/-- Inverse pullback in both arguments of the native real bilinear form. -/
abbrev algebraAutBilinFormAction :
    MulAction (A ≃ₐ[ℝ] A) (LinearMap.BilinForm ℝ A) where
  smul α B := B.comp α.symm.toLinearMap α.symm.toLinearMap
  one_smul B := by
    ext x y
    rfl
  mul_smul α β B := by
    ext x y
    rfl

/-- The functional-action projection is selected with the same scope. -/
abbrev algebraAutFunctionalSMul : SMul (A ≃ₐ[ℝ] A) (A →ₗ[ℝ] ℝ) :=
  (algebraAutFunctionalAction A).toSMul

/-- The form-action projection avoids the unrelated pointwise linear-map action. -/
abbrev algebraAutBilinFormSMul : SMul (A ≃ₐ[ℝ] A) (LinearMap.BilinForm ℝ A) :=
  (algebraAutBilinFormAction A).toSMul

scoped[OperatorInvariantPullback] attribute [instance 2000]
  InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure.algebraAutFunctionalSMul
  InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure.algebraAutBilinFormSMul
  InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure.algebraAutFunctionalAction
  InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure.algebraAutBilinFormAction

open scoped OperatorInvariantPullback

variable {A}

@[simp] theorem algebraAut_functional_smul_apply
    (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ) (x : A) :
    (α • ω) x = ω (α.symm x) := rfl

@[simp] theorem algebraAut_bilinForm_smul_apply
    (α : A ≃ₐ[ℝ] A) (B : LinearMap.BilinForm ℝ A) (x y : A) :
    (α • B) x y = B (α.symm x) (α.symm y) := rfl

/-- Fixed inverse pullback is equivalent to preservation under the forward map. -/
theorem functional_fixed_iff (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ) :
    α • ω = ω ↔ ∀ x, ω (α x) = ω x := by
  constructor
  · intro h x
    have hx := DFunLike.congr_fun h (α x)
    change ω (α.symm (α x)) = ω (α x) at hx
    simpa only [AlgEquiv.symm_apply_apply] using hx.symm
  · intro h
    ext x
    change ω (α.symm x) = ω x
    simpa only [AlgEquiv.apply_symm_apply] using (h (α.symm x)).symm

/-- Both arguments of the form are transported by the same forward map. -/
theorem bilinForm_fixed_iff (α : A ≃ₐ[ℝ] A) (B : LinearMap.BilinForm ℝ A) :
    α • B = B ↔ ∀ x y, B (α x) (α y) = B x y := by
  constructor
  · intro h x y
    have hxy := congrArg (fun C : LinearMap.BilinForm ℝ A => C (α x) (α y)) h
    change B (α.symm (α x)) (α.symm (α y)) = B (α x) (α y) at hxy
    simpa only [AlgEquiv.symm_apply_apply] using hxy.symm
  · intro h
    ext x y
    change B (α.symm x) (α.symm y) = B x y
    simpa only [AlgEquiv.apply_symm_apply] using (h (α.symm x) (α.symm y)).symm

/-- Algebra automorphisms preserving the specified functional and form. -/
def functionalFormAutomorphismSubgroup
    (ω : A →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ A) : Subgroup (A ≃ₐ[ℝ] A) :=
  MulAction.stabilizer (A ≃ₐ[ℝ] A) ω ⊓ MulAction.stabilizer (A ≃ₐ[ℝ] A) B

/-- Membership has the actual forward-preservation equations as its contract. -/
theorem mem_functionalFormAutomorphismSubgroup_iff
    (α : A ≃ₐ[ℝ] A) (ω : A →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ A) :
    α ∈ functionalFormAutomorphismSubgroup ω B ↔
      (∀ x, ω (α x) = ω x) ∧ (∀ x y, B (α x) (α y) = B x y) := by
  change (α • ω = ω ∧ α • B = B) ↔ _
  rw [functional_fixed_iff, bilinForm_fixed_iff]

/-- Adjoining the form to the functional gives their actual product stabilizer. -/
theorem functionalFormAutomorphismSubgroup_eq_stabilizer_pair
    (ω : A →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ A) :
    functionalFormAutomorphismSubgroup ω B =
      MulAction.stabilizer (A ≃ₐ[ℝ] A) (ω, B) := by
  ext α
  change (α • ω = ω ∧ α • B = B) ↔ (α • ω, α • B) = (ω, B)
  constructor
  · rintro ⟨hω, hB⟩
    exact Prod.ext hω hB
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- A subgroup and its invariant-pair closure have the same preservation bound. -/
theorem symmetryClosure_le_functionalForm_iff
    (H : Subgroup (A ≃ₐ[ℝ] A)) (ω : A →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ A) :
    symmetryClosure (A ≃ₐ[ℝ] A)
        ((A →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ A) H ≤
        functionalFormAutomorphismSubgroup ω B ↔
      H ≤ functionalFormAutomorphismSubgroup ω B := by
  rw [functionalFormAutomorphismSubgroup_eq_stabilizer_pair]
  exact symmetryClosure_le_stabilizer_iff H (ω, B)

/-- The full functional/form stabilizer is closed for this invariant carrier. -/
@[simp] theorem symmetryClosure_functionalFormAutomorphismSubgroup
    (ω : A →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ A) :
    symmetryClosure (A ≃ₐ[ℝ] A)
        ((A →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ A)
        (functionalFormAutomorphismSubgroup ω B) =
      functionalFormAutomorphismSubgroup ω B := by
  rw [functionalFormAutomorphismSubgroup_eq_stabilizer_pair, symmetryClosure_stabilizer]

/-- Automorphism families preserving the functional and form generate a subgroup
whose genuine Erlangen closure remains in their common stabilizer. The time
monoid carries no implicit continuity or integration assumption. -/
theorem automorphism_flowFamily_erlangen_closure
    {ι Time : Type*} [Monoid Time]
    (ω : A →ₗ[ℝ] ℝ) (B : LinearMap.BilinForm ℝ A)
    (Φ : ι → Time →* (A ≃ₐ[ℝ] A))
    (hω : ∀ i t x, ω (Φ i t x) = ω x)
    (hB : ∀ i t x y, B (Φ i t x) (Φ i t y) = B x y) :
    flowFamilySubgroup Φ ≤
        symmetryClosure (A ≃ₐ[ℝ] A)
          ((A →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ A) (flowFamilySubgroup Φ) ∧
      symmetryClosure (A ≃ₐ[ℝ] A)
          ((A →ₗ[ℝ] ℝ) × LinearMap.BilinForm ℝ A) (flowFamilySubgroup Φ) ≤
        functionalFormAutomorphismSubgroup ω B := by
  have hfix : ∀ i t, Φ i t • (ω, B) = (ω, B) := by
    intro i t
    exact Prod.ext ((functional_fixed_iff (Φ i t) ω).mpr (hω i t))
      ((bilinForm_fixed_iff (Φ i t) B).mpr (hB i t))
  rw [functionalFormAutomorphismSubgroup_eq_stabilizer_pair]
  exact flowFamilySubgroup_le_symmetryClosure_le_stabilizer Φ (ω, B) hfix

end InfoGeometry.OperatorAlgebra.OperatorInvariantErlangenClosure

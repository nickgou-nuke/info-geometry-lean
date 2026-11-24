/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebraic.CartanSouriauAffineCocycle
import Mathlib.CategoryTheory.Action

/-!
# The native action groupoid of an affine Souriau cocycle

The existing affine action is bundled as `MulAction`; mathlib then supplies
its action category and groupoid. Morphisms have typed endpoints and carry
the group element which takes the source to the target. No smooth, cotangent,
Poisson, or symplectic-groupoid structure is asserted here.
-/

namespace InfoGeometry.Algebraic.CartanSouriauAffineCocycle

open CategoryTheory

variable {G M : Type*} [Group G] [AddCommGroup M]

/-- The already established cocycle action, as a native group action. -/
@[instance_reducible]
def affineMulAction (D : Datum (G := G) (M := M)) : MulAction G M where
  smul := affineAction D
  one_smul := affineAction_one D
  mul_smul := affineAction_mul D

/-- Mathlib's action groupoid specialized to the existing affine cocycle. -/
abbrev AffineActionGroupoid (D : Datum (G := G) (M := M)) :=
  @ActionCategory G _ M (affineMulAction D)

/-- A charge regarded as an object of the native affine action groupoid. -/
def affineActionObject (D : Datum (G := G) (M := M)) (μ : M) :
    AffineActionGroupoid D := by
  letI := affineMulAction D
  exact ActionCategory.objEquiv G M μ

/-- An actual typed arrow, with the group element as its label. -/
def affineActionArrow (D : Datum (G := G) (M := M)) (g : G) (μ : M) :
    affineActionObject D μ ⟶ affineActionObject D (affineAction D g μ) := by
  letI := affineMulAction D
  exact Functor.Elements.homMk g rfl

/-- Two charge objects admit an arrow exactly when they lie in the indicated
affine orbit. The inverse and composition laws are supplied by mathlib's
`Groupoid (ActionCategory G M)` instance. -/
theorem affineActionGroupoid_nonempty_hom_iff
    (D : Datum (G := G) (M := M)) (μ ν : M) :
    Nonempty (affineActionObject D μ ⟶ affineActionObject D ν) ↔
      ∃ g : G, affineAction D g μ = ν := by
  let := affineMulAction D
  constructor
  · rintro ⟨f⟩
    exact ⟨f.hom, f.map_val⟩
  · rintro ⟨g, hg⟩
    exact ⟨Functor.Elements.homMk g hg⟩

/-- An assumed affine-invariant function is constant along typed arrows.
This transports an invariance hypothesis; it does not derive an entropy law. -/
theorem invariant_eq_of_affineActionArrow
    (D : Datum (G := G) (M := M)) {A : Type*} (S : M → A)
    (hS : ∀ (g : G) (μ : M), S (affineAction D g μ) = S μ)
    {μ ν : M} (f : affineActionObject D μ ⟶ affineActionObject D ν) :
    S ν = S μ := by
  obtain ⟨g, hg⟩ := (affineActionGroupoid_nonempty_hom_iff D μ ν).mp ⟨f⟩
  rw [← hg]
  exact hS g μ

end InfoGeometry.Algebraic.CartanSouriauAffineCocycle

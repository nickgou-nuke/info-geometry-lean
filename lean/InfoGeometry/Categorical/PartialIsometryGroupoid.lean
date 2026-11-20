/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NonCommutativeIsometry
import Mathlib.Algebra.Star.StarProjection
import Mathlib.CategoryTheory.Groupoid

/-!
# The groupoid of star projections and supported partial isometries

An arrow from `p` to `q` is an actual element `v` of the ambient star ring
with `v * star v * v = v`, initial projection `star v * v = p`, and final
projection `v * star v = q`. Composition is ordered ambient multiplication:
`v ≫ w` has underlying element `w * v`. Its partial-isometry law is proved
from the matching intermediate projection, using the existing algebra owner.

Adjunction supplies the inverse, so the construction is a native Mathlib
`Groupoid`. The zero projection is retained: its identity is the zero element.
Morphisms are data in `Type`; none of these definitions interpret zero as a
proof of an arbitrary proposition or assert a resource logic for this groupoid.
-/

namespace InfoGeometry.Categorical.PartialIsometryGroupoid

open CategoryTheory InfoGeometry.Algebra.NonCommutativity

universe u

variable (A : Type u) [Ring A] [StarRing A]

/-- Objects are native self-adjoint idempotents in the ambient star ring. -/
def Projection := {p : A // IsStarProjection p}

variable {A}

instance : CoeOut (Projection A) A := ⟨Subtype.val⟩

/-- A support-compatible partial isometry, including its actual ring element. -/
structure Arrow (p q : Projection A) where
  val : A
  partial_isometry : val * star val * val = val
  source_eq : sourceProjection val = (p : A)
  range_eq : rangeProjection val = (q : A)

namespace Arrow

variable {p q r s : Projection A}

@[ext] theorem ext {f g : Arrow p q} (h : f.val = g.val) : f = g := by
  cases f
  cases g
  cases h
  rfl

theorem source_support (f : Arrow p q) : f.val * (p : A) = f.val := by
  rw [← f.source_eq]
  simpa only [sourceProjection, mul_assoc] using f.partial_isometry

theorem range_support (f : Arrow p q) : (q : A) * f.val = f.val := by
  rw [← f.range_eq]
  exact f.partial_isometry

/-- The identity arrow is the object projection, including at zero support. -/
def identity (p : Projection A) : Arrow p p where
  val := p
  partial_isometry := by
    rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq,
      p.property.isIdempotentElem.eq]
  source_eq := by
    change star (p : A) * (p : A) = (p : A)
    rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]
  range_eq := by
    change (p : A) * star (p : A) = (p : A)
    rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]

/-- Category order is first `f`, then `g`; the ring product is `g.val * f.val`. -/
def compose (f : Arrow p q) (g : Arrow q r) : Arrow p r where
  val := g.val * f.val
  partial_isometry := partial_isometry_mul_of_matched_support
    f.partial_isometry g.partial_isometry (g.source_eq.trans f.range_eq.symm)
  source_eq := (sourceProjection_mul_of_matched_support
    f.partial_isometry (g.source_eq.trans f.range_eq.symm)).trans f.source_eq
  range_eq := (rangeProjection_mul_of_matched_support
    g.partial_isometry (g.source_eq.trans f.range_eq.symm)).trans g.range_eq

/-- Adjoint reverses source and target. -/
def adjoint (f : Arrow p q) : Arrow q p where
  val := star f.val
  partial_isometry := by
    simpa only [star_star] using partial_isometry_star f.partial_isometry
  source_eq := by simpa only [sourceProjection, rangeProjection, star_star] using f.range_eq
  range_eq := by simpa only [sourceProjection, rangeProjection, star_star] using f.source_eq

theorem identity_compose (f : Arrow p q) : compose (identity p) f = f := by
  apply ext
  exact f.source_support

theorem compose_identity (f : Arrow p q) : compose f (identity q) = f := by
  apply ext
  exact f.range_support

theorem compose_assoc (f : Arrow p q) (g : Arrow q r) (h : Arrow r s) :
    compose (compose f g) h = compose f (compose g h) := by
  apply ext
  exact (mul_assoc h.val g.val f.val).symm

theorem adjoint_compose (f : Arrow p q) : compose (adjoint f) f = identity q := by
  apply ext
  exact f.range_eq

theorem compose_adjoint (f : Arrow p q) : compose f (adjoint f) = identity p := by
  apply ext
  exact f.source_eq

theorem val_eq_zero_iff_source_eq_zero (f : Arrow p q) :
    f.val = 0 ↔ (p : A) = 0 := by
  constructor
  · intro h
    rw [← f.source_eq, h, sourceProjection, star_zero, zero_mul]
  · intro h
    have hs := f.source_support
    rw [h, mul_zero] at hs
    exact hs.symm

theorem compose_ne_zero (f : Arrow p q) (g : Arrow q r) (hf : f.val ≠ 0) :
    (compose f g).val ≠ 0 :=
  mul_ne_zero_of_matched_support f.partial_isometry
    (g.source_eq.trans f.range_eq.symm) hf

end Arrow

/-- Native category and inverse laws are inherited from the explicit operations above. -/
instance : Groupoid (Projection A) where
  Hom := Arrow
  id := Arrow.identity
  comp := Arrow.compose
  id_comp := Arrow.identity_compose
  comp_id := Arrow.compose_identity
  assoc := Arrow.compose_assoc
  inv := Arrow.adjoint
  inv_comp := Arrow.adjoint_compose
  comp_inv := Arrow.compose_adjoint

@[simp] theorem id_val (p : Projection A) : (𝟙 p : p ⟶ p).val = (p : A) := rfl

@[simp] theorem comp_val {p q r : Projection A} (f : p ⟶ q) (g : q ⟶ r) :
    (f ≫ g).val = g.val * f.val := rfl

@[simp] theorem inv_val {p q : Projection A} (f : p ⟶ q) :
    (Groupoid.inv f).val = star f.val := rfl

/-- The full-support object supplies a canonical model of the arrow type. -/
def unitProjection : Projection A := ⟨1, IsStarProjection.one A⟩

/-- The identity at full support is constructed without assuming any arrow exists. -/
instance unitArrowInhabited :
    Inhabited (Arrow (unitProjection (A := A)) (unitProjection (A := A))) :=
  ⟨Arrow.identity unitProjection⟩

/-- This canonical arrow is nonzero whenever the ambient ring is nontrivial. -/
theorem unitProjection_id_ne_zero [Nontrivial A] :
    (𝟙 (unitProjection (A := A)) : unitProjection (A := A) ⟶ unitProjection (A := A)).val ≠
      (0 : A) := by
  change (1 : A) ≠ 0
  exact one_ne_zero

/-- The zero projection has its valid zero identity arrow. -/
def zeroProjection : Projection A := ⟨0, IsStarProjection.zero A⟩

theorem zeroProjection_id_val :
    (𝟙 (zeroProjection (A := A)) : zeroProjection (A := A) ⟶ zeroProjection (A := A)).val =
      (0 : A) := rfl

/-- An object with a nonzero support has only nonzero outgoing arrows. -/
theorem arrow_ne_zero_of_source_ne_zero {p q : Projection A}
    (hp : (p : A) ≠ 0) (f : p ⟶ q) : f.val ≠ 0 := by
  intro hf
  exact hp (f.val_eq_zero_iff_source_eq_zero.mp hf)

end InfoGeometry.Categorical.PartialIsometryGroupoid

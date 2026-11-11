/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Ring.Equiv

/-!
# Endomorphisms of an idempotent left ideal

For an idempotent `e` in an associative ring, the left module `B e` has
endomorphism ring anti-isomorphic to the unital corner `e B e`.  The opposite
ring in the statement is essential: the endomorphisms act by right
multiplication, whose composition reverses the order of corner products.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The unital corner ring associated to an idempotent. -/
abbrev idempotentCorner (e : B) (he : e * e = e) :=
  (show IsIdempotentElem e from he).Corner

/-- The left `B`-module `B e`. -/
def idempotentLeftIdeal (e : B) (_he : e * e = e) : Submodule B B where
  carrier := {x | x * e = x}
  zero_mem' := by
    change (0 : B) * e = 0
    simp
  add_mem' := by
    intro x y hx hy
    change (x + y) * e = x + y
    rw [add_mul, hx, hy]
  smul_mem' := by
    intro a x hx
    change (a * x) * e = a * x
    rw [mul_assoc, hx]

private lemma idempotentCorner_left (e : B) (he : e * e = e)
    (c : idempotentCorner e he) : e * c.val = c.val := by
  have h := (Subsemigroup.mem_corner_iff (show IsIdempotentElem e from he)).mp c.property
  exact h.1

private lemma idempotentCorner_right (e : B) (he : e * e = e)
    (c : idempotentCorner e he) : c.val * e = c.val := by
  have h := (Subsemigroup.mem_corner_iff (show IsIdempotentElem e from he)).mp c.property
  exact h.2

/-- A corner element acts on `B e` by right multiplication. -/
def idempotentCornerRightMul (e : B) (he : e * e = e)
    (c : (idempotentCorner e he)ᵐᵒᵖ) :
    Module.End B (idempotentLeftIdeal e he) where
  toFun x := ⟨(x : B) * (MulOpposite.unop c).val, by
    change ((x : B) * (MulOpposite.unop c).val) * e = _
    rw [mul_assoc, idempotentCorner_right e he (MulOpposite.unop c)]⟩
  map_add' x y := by
    apply Subtype.ext
    change ((x : B) + (y : B)) * (MulOpposite.unop c).val =
      (x : B) * (MulOpposite.unop c).val + (y : B) * (MulOpposite.unop c).val
    exact add_mul _ _ _
  map_smul' a x := by
    apply Subtype.ext
    change (a * (x : B)) * (MulOpposite.unop c).val =
      a * ((x : B) * (MulOpposite.unop c).val)
    exact mul_assoc _ _ _

/-- The right-multiplication representation as a ring homomorphism from the
opposite corner. -/
def idempotentCornerRightMulHom (e : B) (he : e * e = e) :
    (idempotentCorner e he)ᵐᵒᵖ →+* Module.End B (idempotentLeftIdeal e he) where
  toFun := idempotentCornerRightMul e he
  map_one' := by
    ext x
    change (x : B) * e = (x : B)
    exact x.property
  map_mul' a b := by
    ext x
    simp only [idempotentCornerRightMul, MulOpposite.unop_mul]
    exact (mul_assoc _ _ _).symm
  map_zero' := by
    ext x
    simp only [idempotentCornerRightMul]
    change (x : B) * (0 : B) = 0
    exact mul_zero _
  map_add' a b := by
    ext x
    change (x : B) * ((MulOpposite.unop a).val + (MulOpposite.unop b).val) =
      (x : B) * (MulOpposite.unop a).val + (x : B) * (MulOpposite.unop b).val
    rw [mul_add]

/-- For every idempotent, the endomorphism ring of the left ideal `B e` is
canonically the opposite of the corner `e B e`. -/
noncomputable def idempotentCornerEndEquiv (e : B) (he : e * e = e) :
    (idempotentCorner e he)ᵐᵒᵖ ≃+* Module.End B (idempotentLeftIdeal e he) := by
  apply RingEquiv.ofBijective (idempotentCornerRightMulHom e he)
  constructor
  · intro a b hab
    apply MulOpposite.unop_injective
    apply Subtype.ext
    have h := congrArg (fun f : Module.End B (idempotentLeftIdeal e he) =>
      (f (⟨e, by change e * e = e; exact he⟩ : idempotentLeftIdeal e he) : B)) hab
    change e * (MulOpposite.unop a).val = e * (MulOpposite.unop b).val at h
    rw [idempotentCorner_left e he (MulOpposite.unop a),
      idempotentCorner_left e he (MulOpposite.unop b)] at h
    exact h
  · intro f
    let gen : idempotentLeftIdeal e he := ⟨e, by change e * e = e; exact he⟩
    let c : idempotentCorner e he :=
      ⟨(f gen : B), by
        apply (Subsemigroup.mem_corner_iff (show IsIdempotentElem e from he)).mpr
        constructor
        · have h := f.map_smul e gen
          have hgen : e • gen = gen := by
            apply Subtype.ext
            change e * e = e
            exact he
          have hval := congrArg Subtype.val h
          change (f (e • gen) : B) = e * (f gen : B) at hval
          rw [hgen] at hval
          exact hval.symm
        · exact (f gen).property⟩
    refine ⟨MulOpposite.op c, ?_⟩
    ext x
    have hx : (x : B) = (x : B) * e := x.property.symm
    have hsmul : f ((x : B) • gen) = (x : B) • f gen := f.map_smul (x : B) gen
    have hgen : (x : B) • gen = x := by
      apply Subtype.ext
      change (x : B) * e = (x : B)
      exact x.property
    change (x : B) * c.val = (f x : B)
    calc
      (x : B) * c.val = (x : B) * (f gen : B) := rfl
      _ = (f ((x : B) • gen) : B) := by
        have hsmulVal := congrArg Subtype.val hsmul.symm
        change (x : B) * (f gen : B) =
          (f ((x : B) • gen) : B) at hsmulVal
        exact hsmulVal
      _ = (f x : B) := by rw [hgen]

/-- A right multiplier preserves `B p` precisely when its value on `p` is
supported on the right by `p`. The multiplier itself need not lie in `p B p`. -/
theorem idempotentLeftIdeal_rightMul_preserves_iff
    (p : B) (hp : p * p = p) (a : B) :
    (∀ x ∈ idempotentLeftIdeal p hp,
      x * a ∈ idempotentLeftIdeal p hp) ↔ p * a * p = p * a := by
  change (∀ x : B, x * p = x → (x * a) * p = x * a) ↔
    p * a * p = p * a
  constructor
  · intro h
    exact h p hp
  · intro ha x hx
    calc
      (x * a) * p = ((x * p) * a) * p := by rw [hx]
      _ = x * (p * a * p) := by simp only [mul_assoc]
      _ = x * (p * a) := by rw [ha]
      _ = x * a := by rw [← mul_assoc, hx]

/-- The exact obstruction to preserving the left ideal is its outgoing
off-diagonal corner `p * a * (1 - p)`. -/
theorem idempotentLeftIdeal_rightMul_preserves_iff_mul_one_sub_eq_zero
    (p : B) (hp : p * p = p) (a : B) :
    (∀ x ∈ idempotentLeftIdeal p hp,
      x * a ∈ idempotentLeftIdeal p hp) ↔ p * a * (1 - p) = 0 := by
  rw [idempotentLeftIdeal_rightMul_preserves_iff, mul_sub, mul_one, sub_eq_zero]
  exact eq_comm

/-- Compress an ambient multiplier into the existing native corner. -/
def idempotentCornerCompression (p : B) (hp : p * p = p) (a : B) :
    idempotentCorner p hp :=
  ⟨p * a * p, ⟨a, rfl⟩⟩

@[simp] theorem idempotentCornerCompression_val
    (p : B) (hp : p * p = p) (a : B) :
    (idempotentCornerCompression p hp a).val = p * a * p := rfl

/-- On `B p`, every preserving multiplier acts through its corner
compression. The converse preservation criterion is proved above. -/
theorem idempotentLeftIdeal_mul_cornerCompression
    (p : B) (hp : p * p = p) (a : B) (ha : p * a * p = p * a)
    (x : idempotentLeftIdeal p hp) :
    (x : B) * (idempotentCornerCompression p hp a).val = (x : B) * a := by
  have hx : (x : B) * p = (x : B) := x.property
  change (x : B) * (p * a * p) = (x : B) * a
  rw [ha, ← mul_assoc, hx]

/-- The existing opposite-corner representation is exactly the induced
right multiplication by any ambient multiplier satisfying the criterion. -/
theorem idempotentCornerRightMul_compression_apply
    (p : B) (hp : p * p = p) (a : B) (ha : p * a * p = p * a)
    (x : idempotentLeftIdeal p hp) :
    (idempotentCornerRightMul p hp
      (MulOpposite.op (idempotentCornerCompression p hp a)) x : B) =
      (x : B) * a := by
  change (x : B) * (idempotentCornerCompression p hp a).val = (x : B) * a
  exact idempotentLeftIdeal_mul_cornerCompression p hp a ha x

end InfoGeometry.OperatorAlgebra.PeirceSpine

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.LinearCombination

/-!
# Infinitesimal trilinear stabilizers and operator conjugation

The carrier is the native noncommutative algebra `Module.End R V`.
Its trilinear stabilizer is a native `LieSubalgebra`, with bracket the
composition commutator. A tensor similitude transports this subalgebra
through native `LinearEquiv.lieConj`.

This is the tensor-stabilizer ingredient in Seligman's exceptional
Jordan-algebra construction. It is generic in the trilinear form, and does
not itself identify a particular stabilizer with an exceptional Lie algebra.

Conventions: endomorphisms act on the left, so `e.lieConj D` is
`e ∘ D ∘ e.symm`. The paper's right-action formulas must be translated
accordingly.
-/

namespace InfoGeometry.Algebra.TrilinearStabilizer

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R V W : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The infinitesimal stabilizer of a native curried trilinear form. -/
def trilinearStabilizer (C : V →ₗ[R] V →ₗ[R] V →ₗ[R] R) :
    LieSubalgebra R (Module.End R V) where
  carrier := {D | ∀ x y z,
    C (D x) y z + C x (D y) z + C x y (D z) = 0}
  zero_mem' := by
    intro x y z
    simp
  add_mem' := by
    intro D E hD hE x y z
    simp only [LinearMap.add_apply, map_add]
    linear_combination hD x y z + hE x y z
  smul_mem' := by
    intro r D hD x y z
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    linear_combination r * hD x y z
  lie_mem' := by
    intro D E hD hE x y z
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply, map_sub]
    linear_combination
      hD (E x) y z + hD x (E y) z + hD x y (E z) -
      hE (D x) y z - hE x (D y) z - hE x y (D z)

@[simp]
theorem mem_trilinearStabilizer
    (C : V →ₗ[R] V →ₗ[R] V →ₗ[R] R) (D : Module.End R V) :
    D ∈ trilinearStabilizer C ↔
      ∀ x y z, C (D x) y z + C x (D y) z + C x y (D z) = 0 :=
  Iff.rfl

/-- A tensor similitude transports infinitesimal stabilizers in both directions.

The scale is a unit, so no field, characteristic, or nondegeneracy assumption
is needed for this transport theorem. -/
theorem lieConj_mem_trilinearStabilizer_iff
    (C₁ : V →ₗ[R] V →ₗ[R] V →ₗ[R] R)
    (C₂ : W →ₗ[R] W →ₗ[R] W →ₗ[R] R)
    (e : V ≃ₗ[R] W) (u : Rˣ)
    (hC : ∀ x y z, C₂ (e x) (e y) (e z) = (u : R) * C₁ x y z)
    (D : Module.End R V) :
    e.lieConj D ∈ trilinearStabilizer C₂ ↔ D ∈ trilinearStabilizer C₁ := by
  constructor
  · intro hD x y z
    have h := hD (e x) (e y) (e z)
    simp only [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply] at h
    rw [hC, hC, hC] at h
    apply u.isUnit.mul_left_cancel
    simpa only [mul_add, mul_zero] using h
  · intro hD x y z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := e.surjective z
    simp only [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply]
    rw [hC, hC, hC, ← mul_add, ← mul_add, hD x y z, mul_zero]

/-- Equality of actual Lie-subalgebra images under conjugation. -/
theorem map_trilinearStabilizer_lieConj
    (C₁ : V →ₗ[R] V →ₗ[R] V →ₗ[R] R)
    (C₂ : W →ₗ[R] W →ₗ[R] W →ₗ[R] R)
    (e : V ≃ₗ[R] W) (u : Rˣ)
    (hC : ∀ x y z, C₂ (e x) (e y) (e z) = (u : R) * C₁ x y z) :
    (trilinearStabilizer C₁).map e.lieConj.toLieHom = trilinearStabilizer C₂ := by
  ext D
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact (lieConj_mem_trilinearStabilizer_iff C₁ C₂ e u hC E).2 hE
  · intro hD
    refine ⟨e.lieConj.symm D, ?_, e.lieConj.apply_symm_apply D⟩
    apply (lieConj_mem_trilinearStabilizer_iff C₁ C₂ e u hC _).1
    simpa only [LieEquiv.apply_symm_apply] using hD

/-- The restricted native Lie equivalence associated to a tensor similitude. -/
def trilinearStabilizerLieEquiv
    (C₁ : V →ₗ[R] V →ₗ[R] V →ₗ[R] R)
    (C₂ : W →ₗ[R] W →ₗ[R] W →ₗ[R] R)
    (e : V ≃ₗ[R] W) (u : Rˣ)
    (hC : ∀ x y z, C₂ (e x) (e y) (e z) = (u : R) * C₁ x y z) :
    trilinearStabilizer C₁ ≃ₗ⁅R⁆ trilinearStabilizer C₂ :=
  LieEquiv.ofSubalgebras _ _ e.lieConj
    (map_trilinearStabilizer_lieConj C₁ C₂ e u hC)

@[simp]
theorem trilinearStabilizerLieEquiv_apply
    (C₁ : V →ₗ[R] V →ₗ[R] V →ₗ[R] R)
    (C₂ : W →ₗ[R] W →ₗ[R] W →ₗ[R] R)
    (e : V ≃ₗ[R] W) (u : Rˣ)
    (hC : ∀ x y z, C₂ (e x) (e y) (e z) = (u : R) * C₁ x y z)
    (D : trilinearStabilizer C₁) :
    (trilinearStabilizerLieEquiv C₁ C₂ e u hC D : Module.End R W) =
      e.lieConj (D : Module.End R V) :=
  rfl

end InfoGeometry.Algebra.TrilinearStabilizer

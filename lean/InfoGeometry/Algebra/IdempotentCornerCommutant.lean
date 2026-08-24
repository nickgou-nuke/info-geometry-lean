import Mathlib

/-!
# Endomorphisms of a principal left ideal

For an idempotent `e` in a semiring, the principal left ideal `A e` is an
`A`-module.  Right multiplication by an element of the corner `e A e` gives
an `A`-linear endomorphism of `A e`.  This file proves the elementary
evaluation-at-`e` classification of those endomorphisms.

No primitivity, simplicity, fullness, or Morita equivalence is assumed here.
-/

namespace InfoGeometry.Algebra.IdempotentCornerCommutant

variable {A : Type*} [Semiring A]

noncomputable def principalLeftIdeal (e : A) (he : e * e = e) : Submodule A A where
  carrier := {x | x * e = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x + y) * e = x + y
    rw [add_mul, hx, hy]
  smul_mem' := by
    intro a x hx
    change (a * x) * e = a * x
    rw [mul_assoc, hx]

@[simp] theorem mem_principalLeftIdeal_iff
    (e : A) (he : e * e = e) (x : A) :
    x ∈ principalLeftIdeal e he ↔ x * e = x := Iff.rfl

def corner (e : A) (he : e * e = e) : Type _ :=
  {c : A // c * e = c ∧ e * c = c}

noncomputable def rightCornerMap
    (e : A) (he : e * e = e)
    (c : corner e he) :
    principalLeftIdeal e he →ₗ[A] principalLeftIdeal e he where
  toFun x := ⟨x.1 * c.1, by
    change (x.1 * c.1) * e = x.1 * c.1
    rw [mul_assoc, c.2.1]
  ⟩
  map_add' x y := by
    ext
    simp [add_mul]
  map_smul' a x := by
    ext
    simp [smul_eq_mul, mul_assoc]

theorem rightCornerMap_apply
    (e : A) (he : e * e = e)
    (c : corner e he)
    (x : principalLeftIdeal e he) :
    rightCornerMap e he c x = ⟨x.1 * c.1, by
      change (x.1 * c.1) * e = x.1 * c.1
      rw [mul_assoc, c.2.1]
    ⟩ := rfl

noncomputable def corner_of_idempotent_endomorphism
    (e : A) (he : e * e = e)
    (T : Module.End A (principalLeftIdeal e he)) :
    corner e he := by
  refine ⟨T ⟨e, he⟩, (T ⟨e, he⟩).property, ?_⟩
  have h := T.map_smul e (⟨e, he⟩ : principalLeftIdeal e he)
  have he' : e • (⟨e, he⟩ : principalLeftIdeal e he) = ⟨e, he⟩ := by
    apply Subtype.ext
    simp [smul_eq_mul, he]
  rw [he'] at h
  have hc := congrArg
    (fun z : principalLeftIdeal e he => (z : A)) h.symm
  simpa only [smul_eq_mul] using hc

theorem corner_endomorphism_eq_rightCornerMap
    (e : A) (he : e * e = e)
    (T : Module.End A (principalLeftIdeal e he)) :
    T = rightCornerMap e he
      (corner_of_idempotent_endomorphism e he T) := by
  apply LinearMap.ext
  intro x
  have hx : x.1 = x.1 * e := x.2.symm
  calc
    T x = T (x.1 • (⟨e, he⟩ : principalLeftIdeal e he)) := by
      congr 1
      apply Subtype.ext
      change x.1 = x.1 * e
      exact hx
    _ = x.1 • T ⟨e, he⟩ := by
      rw [map_smul]
    _ = rightCornerMap e he
      (corner_of_idempotent_endomorphism e he T) x := by
      rfl

/-! The evaluation-at-the-idempotent argument also makes the corner action
injective.  No primitivity or fullness hypothesis is needed. -/

theorem rightCornerMap_injective
    (e : A) (he : e * e = e) :
    Function.Injective (rightCornerMap e he) := by
  intro c d hcd
  apply Subtype.ext
  have h := LinearMap.congr_fun hcd (⟨e, he⟩ : principalLeftIdeal e he)
  have h' := congrArg Subtype.val h
  simpa [rightCornerMap_apply, c.2.2, d.2.2] using h'

/-- The corner is exactly the endomorphism carrier of the principal left ideal.

This is an equivalence of carriers.  It does not identify the corner with a
field or assert any Morita fullness property. -/
noncomputable def cornerEndEquiv
    (e : A) (he : e * e = e) :
    corner e he ≃ Module.End A (principalLeftIdeal e he) where
  toFun := rightCornerMap e he
  invFun := corner_of_idempotent_endomorphism e he
  left_inv := by
    intro c
    apply Subtype.ext
    have h := congrArg Subtype.val
      (rightCornerMap_apply e he c (⟨e, he⟩ : principalLeftIdeal e he))
    simpa [c.2.2] using h
  right_inv := by
    intro T
    exact (corner_endomorphism_eq_rightCornerMap e he T).symm

end InfoGeometry.Algebra.IdempotentCornerCommutant

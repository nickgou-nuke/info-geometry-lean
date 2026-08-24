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

noncomputable def cornerMul
    (e : A) (he : e * e = e)
    (c d : corner e he) : corner e he :=
  ⟨c.1 * d.1, by
    constructor
    · rw [mul_assoc, d.2.1]
    · rw [← mul_assoc, c.2.2]⟩

noncomputable def cornerOne
    (e : A) (he : e * e = e) : corner e he :=
  ⟨e, he, he⟩

noncomputable def cornerZero
    (e : A) (he : e * e = e) : corner e he :=
  ⟨0, by simp, by simp⟩

/-- An idempotent is primitive when it has no nonzero proper idempotent
subelement.  This is only a predicate; no primitivity is assumed globally. -/
def IsPrimitiveIdempotent (e : A) (he : e * e = e) : Prop :=
  ∀ f : A, f * f = f → f * e = f → e * f = f →
    f = 0 ∨ f = e

theorem cornerMul_assoc
    (e : A) (he : e * e = e)
    (a b c : corner e he) :
    cornerMul e he (cornerMul e he a b) c =
      cornerMul e he a (cornerMul e he b c) := by
  apply Subtype.ext
  exact mul_assoc a.1 b.1 c.1

theorem cornerMul_one
    (e : A) (he : e * e = e)
    (a : corner e he) :
    cornerMul e he a (cornerOne e he) = a := by
  apply Subtype.ext
  exact a.2.1

theorem cornerOne_mul
    (e : A) (he : e * e = e)
    (a : corner e he) :
    cornerMul e he (cornerOne e he) a = a := by
  apply Subtype.ext
  exact a.2.2

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

theorem rightCornerMap_comp_apply
    (e : A) (he : e * e = e)
    (c d : corner e he)
    (x : principalLeftIdeal e he) :
    rightCornerMap e he c (rightCornerMap e he d x) =
      rightCornerMap e he (cornerMul e he d c) x := by
  apply Subtype.ext
  simp only [rightCornerMap_apply]
  change (x.1 * d.1) * c.1 = x.1 * (d.1 * c.1)
  rw [mul_assoc]

theorem rightCornerMap_comp
    (e : A) (he : e * e = e)
    (c d : corner e he) :
    (rightCornerMap e he c).comp (rightCornerMap e he d) =
      rightCornerMap e he (cornerMul e he d c) := by
  ext x
  simpa [LinearMap.comp_apply] using rightCornerMap_comp_apply e he c d x

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

theorem cornerEndEquiv_cornerOne
    (e : A) (he : e * e = e) :
    cornerEndEquiv e he (cornerOne e he) =
      (LinearMap.id : Module.End A (principalLeftIdeal e he)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.1 * e = x.1
  exact x.2

theorem cornerEndEquiv_cornerZero
    (e : A) (he : e * e = e) :
    cornerEndEquiv e he (cornerZero e he) =
      (0 : Module.End A (principalLeftIdeal e he)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [cornerEndEquiv, cornerZero, rightCornerMap_apply]

theorem idempotent_endomorphism_eq_zero_or_id_of_primitive
    (e : A) (he : e * e = e)
    (hprimitive : IsPrimitiveIdempotent e he)
    (T : Module.End A (principalLeftIdeal e he))
    (hT : T.comp T = T) :
    T = 0 ∨ T = (LinearMap.id : Module.End A (principalLeftIdeal e he)) := by
  let c : corner e he := corner_of_idempotent_endomorphism e he T
  have hc : cornerMul e he c c = c := by
    apply (cornerEndEquiv e he).injective
    calc
      cornerEndEquiv e he (cornerMul e he c c) =
          (cornerEndEquiv e he c).comp (cornerEndEquiv e he c) := by
        simpa [cornerEndEquiv] using
          (rightCornerMap_comp e he c c).symm
      _ = T.comp T := by
        rw [show cornerEndEquiv e he c = T by
          simpa [cornerEndEquiv] using
            (corner_endomorphism_eq_rightCornerMap e he T).symm]
      _ = T := hT
      _ = cornerEndEquiv e he c :=
        by simpa [cornerEndEquiv] using
          (corner_endomorphism_eq_rightCornerMap e he T)
  have hcorner : c = cornerZero e he ∨ c = cornerOne e he := by
    have hsub_left : c.1 * e = c.1 := c.2.1
    have hsub_right : e * c.1 = c.1 := c.2.2
    rcases hprimitive c.1 (by
      simpa [cornerMul] using congrArg Subtype.val hc) hsub_left hsub_right with h | h
    · left
      apply Subtype.ext
      simpa [cornerZero] using h
    · right
      apply Subtype.ext
      simpa [cornerOne] using h
  rcases hcorner with h | h
  · left
    rw [← cornerEndEquiv_cornerZero e he]
    simpa [cornerEndEquiv] using
      (show T = cornerEndEquiv e he (cornerZero e he) by
        calc
          T = cornerEndEquiv e he c := by
            simpa [cornerEndEquiv] using
              (corner_endomorphism_eq_rightCornerMap e he T)
          _ = cornerEndEquiv e he (cornerZero e he) := congrArg (cornerEndEquiv e he) h)
  · right
    rw [← cornerEndEquiv_cornerOne e he]
    simpa [cornerEndEquiv] using
      (show T = cornerEndEquiv e he (cornerOne e he) by
        calc
          T = cornerEndEquiv e he c := by
            simpa [cornerEndEquiv] using
              (corner_endomorphism_eq_rightCornerMap e he T)
          _ = cornerEndEquiv e he (cornerOne e he) := congrArg (cornerEndEquiv e he) h)

/-! The endomorphism equivalence is contravariant for corner
multiplication: composition of right multiplications reverses the corner
factors.  This is the concrete opposite-algebra law; no primitivity or
fullness is involved. -/

theorem cornerEndEquiv_comp
    (e : A) (he : e * e = e)
    (c d : corner e he) :
    cornerEndEquiv e he (cornerMul e he d c) =
      (cornerEndEquiv e he c).comp (cornerEndEquiv e he d) := by
  simpa [cornerEndEquiv] using (rightCornerMap_comp e he c d).symm

/-! Evaluation at `e` exposes the opposite multiplication law directly:
the corner representative of a composite endomorphism is obtained by
reversing the corner factors.  This is the reusable Morita statement before
bundling any additional algebra structure on the corner carrier. -/
theorem corner_of_comp
    (e : A) (he : e * e = e)
    (T S : Module.End A (principalLeftIdeal e he)) :
    corner_of_idempotent_endomorphism e he (T.comp S) =
      cornerMul e he
        (corner_of_idempotent_endomorphism e he S)
        (corner_of_idempotent_endomorphism e he T) := by
  apply (cornerEndEquiv e he).injective
  calc
    cornerEndEquiv e he
        (corner_of_idempotent_endomorphism e he (T.comp S)) =
        T.comp S := (cornerEndEquiv e he).right_inv (T.comp S)
    _ = cornerEndEquiv e he
        (cornerMul e he
          (corner_of_idempotent_endomorphism e he S)
          (corner_of_idempotent_endomorphism e he T)) := by
      rw [cornerEndEquiv_comp]
      have hT : cornerEndEquiv e he
          (corner_of_idempotent_endomorphism e he T) = T := by
        exact (corner_endomorphism_eq_rightCornerMap e he T).symm
      have hS : cornerEndEquiv e he
          (corner_of_idempotent_endomorphism e he S) = S := by
        exact (corner_endomorphism_eq_rightCornerMap e he S).symm
      rw [hT, hS]

end InfoGeometry.Algebra.IdempotentCornerCommutant

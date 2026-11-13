/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# An additive projection onto the existing lower-support subring

The native three-corner subring, specialized at idempotents `(0,p)`, is
exactly the set of operators whose upper Peirce corner vanishes. The map
`x ↦ x - conePlus p x` is an additive idempotent projection onto this native
subring. Its codomain restriction is a surjective additive homomorphism.

Multiplication, powers, and finite products stay in the image because it is
a subring. The projection itself is not asserted to be multiplicative, and
no temporal or star-closed interpretation is assigned to its support.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceLowerProjection

open PeirceSpine ThreeCornerColumnAlgebra

variable {B : Type*} [Ring B]

/-- The lower-support specialization of the already constructed native subring. -/
def lowerSupportSubring (p : B) (hp : p * p = p) : Subring B :=
  supportedSubring (p := (0 : B)) (l := p) (by simp) hp (by simp) (by simp)

/-- The existing subring is exactly the kernel of the upper-corner extraction. -/
@[simp]
theorem mem_lowerSupportSubring (p : B) (hp : p * p = p) (x : B) :
    x ∈ lowerSupportSubring p hp ↔ conePlus p x = 0 := by
  change (∃ F L Q, x = columnOp (0 : B) p F L Q) ↔ conePlus p x = 0
  constructor
  · rintro ⟨F, L, Q, rfl⟩
    have h := forbidden_corners (p := (0 : B)) (l := p)
      (by simp) hp (by simp) (by simp) F L Q
    simpa only [conePlus, third, sub_zero] using h.2.1
  · intro hx
    refine ⟨0, x, x, ?_⟩
    calc
      x = columnOp (0 : B) p 0 x x + conePlus p x := by
        unfold columnOp third peirce11 conePlus
        noncomm_ring
      _ = columnOp (0 : B) p 0 x x := by rw [hx, add_zero]

/-- Remove only the upper off-diagonal corner, retaining the operator carrier. -/
def lowerProjection (p : B) : B →+ B where
  toFun x := x - conePlus p x
  map_zero' := by simp only [conePlus_zero, sub_self]
  map_add' x y := by
    rw [conePlus_add]
    abel

@[simp]
theorem lowerProjection_apply (p x : B) :
    lowerProjection p x = x - conePlus p x := rfl

/-- The projection is the three retained Peirce corners from the intake. -/
theorem lowerProjection_eq_corners (p x : B) :
    lowerProjection p x = peirce11 p x + peirce00 p x + coneMinus p x := by
  change x - conePlus p x = _
  unfold peirce11 peirce00 conePlus coneMinus
  noncomm_ring

theorem conePlus_lowerProjection {p : B} (hp : p * p = p) (x : B) :
    conePlus p (lowerProjection p x) = 0 := by
  have hc : conePlus p (conePlus p x) = conePlus p x := by
    change p * conePlus p x * (1 - p) = conePlus p x
    rw [P_mul_conePlus hp, mul_sub, mul_one, conePlus_mul_P hp, sub_zero]
  rw [lowerProjection_apply, conePlus_sub, hc, sub_self]

/-- Fixed points are characterized without an idempotency assumption. -/
theorem lowerProjection_fixed_iff (p x : B) :
    lowerProjection p x = x ↔ conePlus p x = 0 := by
  change x - conePlus p x = x ↔ conePlus p x = 0
  exact sub_eq_self

theorem lowerProjection_mem {p : B} (hp : p * p = p) (x : B) :
    lowerProjection p x ∈ lowerSupportSubring p hp :=
  (mem_lowerSupportSubring p hp _).mpr (conePlus_lowerProjection hp x)

/-- The fixed-point carrier is the existing native subring. -/
theorem lowerProjection_fixed_iff_mem {p : B} (hp : p * p = p) (x : B) :
    lowerProjection p x = x ↔ x ∈ lowerSupportSubring p hp :=
  (lowerProjection_fixed_iff p x).trans (mem_lowerSupportSubring p hp x).symm

theorem lowerProjection_idempotent {p : B} (hp : p * p = p) (x : B) :
    lowerProjection p (lowerProjection p x) = lowerProjection p x :=
  (lowerProjection_fixed_iff p _).mpr (conePlus_lowerProjection hp x)

/-- Equality of native additive subgroups, not just inclusion of selected examples. -/
theorem lowerProjection_range {p : B} (hp : p * p = p) :
    (lowerProjection p).range = (lowerSupportSubring p hp).toAddSubgroup := by
  ext x
  change (∃ y, lowerProjection p y = x) ↔ x ∈ lowerSupportSubring p hp
  constructor
  · rintro ⟨y, rfl⟩
    exact lowerProjection_mem hp y
  · intro hx
    exact ⟨x, (lowerProjection_fixed_iff_mem hp x).mpr hx⟩

/-- The constructed additive map with its actual native subring codomain. -/
def lowerProjectionTo (p : B) (hp : p * p = p) : B →+ lowerSupportSubring p hp where
  toFun x := ⟨lowerProjection p x, lowerProjection_mem hp x⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (lowerProjection p)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (lowerProjection p) x y

@[simp]
theorem lowerProjectionTo_coe (p : B) (hp : p * p = p) (x : B) :
    (lowerProjectionTo p hp x : B) = lowerProjection p x := rfl

/-- The projection restricts to the identity on its constructed codomain. -/
theorem lowerProjectionTo_retract (p : B) (hp : p * p = p)
    (x : lowerSupportSubring p hp) : lowerProjectionTo p hp (x : B) = x := by
  apply Subtype.ext
  exact (lowerProjection_fixed_iff_mem hp (x : B)).mpr x.property

theorem lowerProjectionTo_surjective (p : B) (hp : p * p = p) :
    Function.Surjective (lowerProjectionTo p hp) := by
  intro x
  exact ⟨(x : B), lowerProjectionTo_retract p hp x⟩

/-- Multiplication of two projected inputs stays fixed, by native subring closure. -/
theorem lowerProjection_mul_fixed {p : B} (hp : p * p = p) (x y : B) :
    lowerProjection p (lowerProjection p x * lowerProjection p y) =
      lowerProjection p x * lowerProjection p y :=
  (lowerProjection_fixed_iff_mem hp _).mpr
    ((lowerSupportSubring p hp).mul_mem
      (lowerProjection_mem hp x) (lowerProjection_mem hp y))

theorem lowerProjection_pow_fixed {p : B} (hp : p * p = p) (x : B) (n : ℕ) :
    lowerProjection p ((lowerProjection p x) ^ n) = (lowerProjection p x) ^ n :=
  (lowerProjection_fixed_iff_mem hp _).mpr
    ((lowerSupportSubring p hp).pow_mem (lowerProjection_mem hp x) n)

/-- Heterogeneous finite compositions preserve lower support. -/
theorem lowerProjection_list_prod_fixed {p : B} (hp : p * p = p) (xs : List B)
    (hxs : ∀ x ∈ xs, lowerProjection p x = x) :
    lowerProjection p xs.prod = xs.prod :=
  (lowerProjection_fixed_iff_mem hp _).mpr
    ((lowerSupportSubring p hp).list_prod_mem
      (fun x hx => (lowerProjection_fixed_iff_mem hp x).mp (hxs x hx)))

end InfoGeometry.OperatorAlgebra.PeirceLowerProjection

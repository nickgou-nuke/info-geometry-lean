/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenrose
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic

/-!
# Moore-Penrose support sectors

`false` selects a support projection and `true` its complement. The four
Boolean sectors sum to one universally. They are pairwise orthogonal star
projections when the two support projections commute. No nilpotency hypothesis
can replace that commutation condition in general.
-/

namespace InfoGeometry.Singular.MoorePenroseSectors

open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R]

/-- A support projector or its complement. -/
def part (p : R) : Bool → R
  | false => p
  | true => 1 - p

/-- The four ordered sectors: interior, sink, source, common null. -/
def sector (p q : R) (b : Bool × Bool) : R := part p b.1 * part q b.2

/-- This algebraic identity does not require projection or inverse equations. -/
theorem partition (p q : R) :
    sector p q (false, false) + sector p q (false, true) +
      sector p q (true, false) + sector p q (true, true) = 1 := by
  simp only [sector, part]
  noncomm_ring

lemma part_mul {p : R} (hp : p * p = p) (i j : Bool) :
    part p i * part p j = if i = j then part p i else 0 := by
  cases i <;> cases j <;> simp [part, mul_sub, sub_mul, hp]

lemma part_commute {p q : R} (h : Commute p q) (i j : Bool) :
    Commute (part p i) (part q j) := by
  cases i <;> cases j
  · exact h
  · change p * (1 - q) = (1 - q) * p
    rw [mul_sub, sub_mul, mul_one, one_mul, h.eq]
  · change (1 - p) * q = q * (1 - p)
    rw [mul_sub, sub_mul, mul_one, one_mul, h.eq]
  · change (1 - p) * (1 - q) = (1 - q) * (1 - p)
    simp only [mul_sub, sub_mul, mul_one, one_mul]
    rw [h.eq]
    abel

/-- Full multiplication table, not just the sum-to-one identity. -/
theorem sector_mul {p q : R} (hp : p * p = p) (hq : q * q = q)
    (h : Commute p q) (i j : Bool × Bool) :
    sector p q i * sector p q j = if i = j then sector p q i else 0 := by
  calc
    sector p q i * sector p q j =
        part p i.1 * (part q i.2 * part p j.1) * part q j.2 := by
          simp only [sector, mul_assoc]
    _ = part p i.1 * (part p j.1 * part q i.2) * part q j.2 := by
      rw [← (part_commute h j.1 i.2).eq]
    _ = (part p i.1 * part p j.1) * (part q i.2 * part q j.2) := by
      simp only [mul_assoc]
    _ = if i = j then sector p q i else 0 := by
      rw [part_mul hp, part_mul hq]
      by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
        simp [h₁, h₂, Prod.ext_iff, sector]

/-- The failure of the boundary-square identity is precisely noncommutation. -/
theorem boundary_square_defect {p q : R} (hp : p * p = p) (hq : q * q = q) :
    (p * (1 - q) + (1 - p) * q) - (p - q) ^ 2 = q * p - p * q := by
  noncomm_ring [hp, hq]

theorem boundary_eq_square_iff {p q : R} (hp : p * p = p) (hq : q * q = q) :
    p * (1 - q) + (1 - p) * q = (p - q) ^ 2 ↔ Commute p q := by
  rw [← sub_eq_zero, boundary_square_defect hp hq, sub_eq_zero]
  exact eq_comm

theorem jordan_identity {p q : R} (hp : p * p = p) (hq : q * q = q)
    (h : Commute p q) : p + q = 2 • (p * q) + (p - q) ^ 2 := by
  rw [← (boundary_eq_square_iff hp hq).mpr h, two_smul]
  noncomm_ring

theorem three_sector_partition {p q : R} (hp : p * p = p) (hq : q * q = q)
    (h : Commute p q) : p * q + (p - q) ^ 2 + (1 - p) * (1 - q) = 1 := by
  rw [← (boundary_eq_square_iff hp hq).mpr h]
  noncomm_ring

section Star
variable [StarRing R]

lemma part_isStarProjection {p : R} (hp : IsStarProjection p) (i : Bool) :
    IsStarProjection (part p i) := by
  cases i
  · exact hp
  · exact hp.one_sub

theorem sector_isStarProjection {p q : R}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : Commute p q)
    (i : Bool × Bool) : IsStarProjection (sector p q i) :=
  (part_isStarProjection hp i.1).mul (part_isStarProjection hq i.2)
    (part_commute h i.1 i.2)

theorem boundary_isStarProjection {p q : R}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : Commute p q) :
    IsStarProjection ((p - q) ^ 2) := by
  rw [← (boundary_eq_square_iff hp.isIdempotentElem hq.isIdempotentElem).mpr h]
  exact (sector_isStarProjection hp hq h (false, true)).add
    (sector_isStarProjection hp hq h (true, false))
    (by simpa using (sector_mul hp.isIdempotentElem hq.isIdempotentElem h
      (false, true) (true, false)))

/-- The actual Penrose laws supply native star projections. -/
theorem support_isStarProjection {x m : R} (hm : IsMoorePenroseInverse x m) :
    IsStarProjection (x * m) ∧ IsStarProjection (m * x) := by
  constructor
  · refine (isStarProjection_iff').mpr ⟨?_, hm.ab_adj_eq⟩
    calc
      (x * m) * (x * m) = (x * m * x) * m := by simp only [mul_assoc]
      _ = x * m := by rw [hm.aba_eq_a]
  · refine (isStarProjection_iff').mpr ⟨?_, hm.ba_adj_eq⟩
    calc
      (m * x) * (m * x) = (m * x * m) * x := by simp only [mul_assoc]
      _ = m * x := by rw [hm.bab_eq_b]

/-- This particular commutator is self-adjoint, not skew-adjoint. -/
theorem mp_commutator_selfAdjoint {x m : R} (hm : IsMoorePenroseInverse x m) :
    IsSelfAdjoint (x * m - m * x) := by
  change star (x * m - m * x) = x * m - m * x
  rw [star_sub, hm.ab_adj_eq, hm.ba_adj_eq]

/-- Complete MP sector certificate derived from the four Penrose equations. -/
theorem mp_sector_projections {x m : R} (hm : IsMoorePenroseInverse x m)
    (hc : Commute (x * m) (m * x)) :
    (∀ i, IsStarProjection (sector (x * m) (m * x) i)) ∧
    (∀ i j, i ≠ j → sector (x * m) (m * x) i * sector (x * m) (m * x) j = 0) := by
  obtain ⟨hp, hq⟩ := support_isStarProjection hm
  refine ⟨sector_isStarProjection hp hq hc, ?_⟩
  intro i j hij
  rw [sector_mul hp.isIdempotentElem hq.isIdempotentElem hc, ite_eq_right hij]

end Star

/-- Universal refinement is only an algebraic partition before compatibility. -/
theorem refinement_partition (e p q : R) :
    (1 - e) + e * sector p q (false, false) + e * sector p q (false, true) +
      e * sector p q (true, false) + e * sector p q (true, true) = 1 := by
  simp only [sector, part]
  noncomm_ring

lemma commute_sector {e p q : R} (hp : Commute e p) (hq : Commute e q)
    (i : Bool × Bool) : Commute e (sector p q i) :=
  (part_commute hp false i.1).mul_right (part_commute hq false i.2)

/-- A sufficient compatibility condition for an orthogonal ambient refinement. -/
theorem refinement_isStarProjection [StarRing R] {e p q : R}
    (he : IsStarProjection e) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) (hep : Commute e p) (heq : Commute e q)
    (i : Bool × Bool) : IsStarProjection (e * sector p q i) :=
  he.mul (sector_isStarProjection hp hq hpq i) (commute_sector hep heq i)

end InfoGeometry.Singular.MoorePenroseSectors

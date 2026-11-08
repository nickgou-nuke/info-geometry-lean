/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MetricAlgebraicProjectionDefect
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing

/-!
# Support sectors with the noncommutation defect retained

The four-term sum is unconditional. Projection and orthogonality conclusions
require commuting supports. `boundary_square_defect` retains the obstruction;
`refinement_idempotence_defect` retains the obstruction to a further Drazin
refinement. These are ring identities, applicable to graph operators on their
actual operator carrier; no graph boundary interpretation is assumed.
-/

namespace InfoGeometry.Singular.ProjectionSectors

open MetricAlgebraicProjectionDefect

variable {R : Type*} [Ring R] {p q e : R}

/-- Ordered four-sector resolution, without commutativity or idempotence. -/
theorem four_sector_sum (p q : R) :
    p * q + p * (1 - q) + (1 - p) * q + (1 - p) * (1 - q) = 1 := by
  noncomm_ring

/-- The correction to the proposed boundary square is exactly the commutator. -/
theorem boundary_square_defect (hp : p * p = p) (hq : q * q = q) :
    (p - q)^2 - (p * (1 - q) + (1 - p) * q) = commutatorDefect p q := by
  unfold commutatorDefect
  noncomm_ring [hp, hq]

/-- Without commuting supports the three-sector sum retains a defect term. -/
theorem three_sector_sum_with_defect (hp : p * p = p) (hq : q * q = q) :
    p * q + (p - q)^2 + (1 - p) * (1 - q) = 1 + commutatorDefect p q := by
  unfold commutatorDefect
  noncomm_ring [hp, hq]

/-- The sum of supports counts the common sector twice, with a defect correction. -/
theorem support_sum_with_defect (hp : p * p = p) (hq : q * q = q) :
    p + q = 2 • (p * q) + (p - q)^2 - commutatorDefect p q := by
  unfold commutatorDefect
  simp only [two_smul]
  noncomm_ring [hp, hq]

/-- A product of idempotents fails idempotence by a sandwiched commutator. -/
theorem refinement_idempotence_defect (he : e * e = e) (hp : p * p = p) :
    (e * p) * (e * p) - e * p = -e * commutatorDefect e p * p := by
  unfold commutatorDefect
  have heep : e * (e * p) = e * p := by
    rw [← mul_assoc, he]
  simp only [mul_sub, sub_mul, neg_mul]
  rw [heep]
  noncomm_ring [he, hp]

/-- A commutator transports a triple product by the Leibniz rule in all slots. -/
theorem commutator_triple_product (e x y z : R) :
    commutatorDefect e (x * y * z) =
      commutatorDefect e x * y * z + x * commutatorDefect e y * z +
        x * y * commutatorDefect e z := by
  unfold commutatorDefect
  noncomm_ring

/-- Refinement of the three-sector sum by an oblique idempotent retains its defect. -/
theorem refined_sum_with_defect (e : R) (hp : p * p = p) (hq : q * q = q) :
    (1 - e) + e * (p * q) + e * (p - q)^2 + e * ((1 - p) * (1 - q)) =
      1 + e * commutatorDefect p q := by
  have h := congrArg (fun x => e * x) (three_sector_sum_with_defect hp hq)
  simp only [mul_add, mul_one] at h
  calc
    _ = (1 - e) + (e * (p * q) + e * (p - q)^2 +
        e * ((1 - p) * (1 - q))) := by noncomm_ring
    _ = _ := by rw [h]; noncomm_ring

section Star
variable [StarRing R]

/-- Moore–Penrose range and domain supports are star projections. -/
theorem mp_supports {a m : R} (h : MoorePenrose.IsMoorePenroseInverse a m) :
    IsStarProjection (a * m) ∧ IsStarProjection (m * a) := by
  constructor
  · rw [isStarProjection_iff']
    exact ⟨by simpa [mul_assoc] using congrArg (fun x => x * m) h.aba_eq_a,
      h.ab_adj_eq⟩
  · rw [isStarProjection_iff']
    exact ⟨by simpa [mul_assoc] using congrArg (fun x => x * a) h.bab_eq_b,
      h.ba_adj_eq⟩

/-- Commuting support projections give star projections for all four sectors. -/
theorem four_sector_projections (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : Commute p q) :
    IsStarProjection (p * q) ∧ IsStarProjection (p * (1 - q)) ∧
    IsStarProjection ((1 - p) * q) ∧ IsStarProjection ((1 - p) * (1 - q)) := by
  have hpnq : Commute p (1 - q) := by
    show p * (1 - q) = (1 - q) * p
    noncomm_ring [h.eq]
  have hnpq : Commute (1 - p) q := by
    show (1 - p) * q = q * (1 - p)
    noncomm_ring [h.eq]
  have hnpnq : Commute (1 - p) (1 - q) := by
    show (1 - p) * (1 - q) = (1 - q) * (1 - p)
    noncomm_ring [h.eq]
  exact ⟨hp.mul hq h, hp.mul hq.one_sub hpnq,
    hp.one_sub.mul hq hnpq, hp.one_sub.mul hq.one_sub hnpnq⟩

/-- The boundary square is a star projection under the commutation hypothesis. -/
theorem boundary_square_projection (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : Commute p q) : IsStarProjection ((p - q)^2) := by
  obtain ⟨_, hs, ht, _⟩ := four_sector_projections hp hq h
  have hcomp : (1 - q) * (1 - p) = (1 - p) * (1 - q) := by
    noncomm_ring [h.eq]
  have hst : (p * (1 - q)) * ((1 - p) * q) = 0 := by
    calc
      (p * (1 - q)) * ((1 - p) * q) =
          p * (((1 - q) * (1 - p)) * q) := by
            simp only [mul_assoc]
      _ = p * (((1 - p) * (1 - q)) * q) := by rw [hcomp]
      _ = 0 := by
        noncomm_ring [hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  have hb := boundary_square_defect hp.isIdempotentElem.eq hq.isIdempotentElem.eq
  have hc : commutatorDefect p q = 0 := sub_eq_zero.mpr h.eq
  rw [hc, sub_eq_zero] at hb
  rw [hb]
  exact hs.add ht hst

omit [StarRing R] in
/-- The three sectors sum to one precisely when the support commutator vanishes. -/
theorem three_sector_sum_iff_commute (hp : p * p = p) (hq : q * q = q) :
    p * q + (p - q)^2 + (1 - p) * (1 - q) = 1 ↔ Commute p q := by
  rw [three_sector_sum_with_defect hp hq, add_eq_left]
  exact sub_eq_zero

end Star
/-- The boundary square fails idempotence by the square of the support commutator. -/
theorem boundary_idempotence_defect (hp : p * p = p) (hq : q * q = q) :
    ((p - q)^2)^2 - (p - q)^2 = (commutatorDefect p q)^2 := by
  have hpp (x : R) : p * (p * x) = p * x := by rw [← mul_assoc, hp]
  have hqq (x : R) : q * (q * x) = q * x := by rw [← mul_assoc, hq]
  unfold commutatorDefect
  noncomm_ring [hp, hq]
  simp only [hpp, hqq]
  abel

/-- Compression leakage is the exact obstruction to preserving idempotence. -/
theorem compression_idempotence_defect (he : e * e = e) (hp : p * p = p) :
    (e * p * e) * (e * p * e) - e * p * e = -e * p * (1 - e) * p * e := by
  have hee (x : R) : e * (e * x) = e * x := by rw [← mul_assoc, he]
  noncomm_ring [he, hp]
  simp only [hee]
  abel

/-- The three commuting support sectors annihilate one another. -/
theorem three_sector_orthogonal (hp : p * p = p) (hq : q * q = q)
    (h : Commute p q) :
    (p * q) * (p - q)^2 = 0 ∧
    (p * q) * ((1 - p) * (1 - q)) = 0 ∧
    (p - q)^2 * ((1 - p) * (1 - q)) = 0 := by
  have hqq (x : R) : q * (q * x) = q * x := by rw [← mul_assoc, hq]
  have hpqp : p * (q * p) = q * p := by rw [← mul_assoc, h.eq, mul_assoc, hp]
  constructor
  · noncomm_ring [hp, hq, h.eq]
    simp only [hqq, hpqp]
    abel
  constructor <;> noncomm_ring [hp, hq, h.eq] <;> simp only [hqq, hpqp] <;> abel

end InfoGeometry.Singular.ProjectionSectors

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
  cases i <;> cases j <;> (show part p _ * part q _ = part q _ * part p _; simp only [part]; noncomm_ring [h.eq])

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
  have hmul := sector_mul hp.isIdempotentElem hq.isIdempotentElem h (false, true) (true, false)
  exact (sector_isStarProjection hp hq h (false, true)).add
    (sector_isStarProjection hp hq h (true, false))
    (by simpa [sector, part] using hmul)

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
  rw [sector_mul hp.isIdempotentElem hq.isIdempotentElem hc, ite_eq_right_iff.mpr (fun h => False.elim (hij h))]

end Star

/-- Universal refinement is only an algebraic partition before compatibility. -/
theorem refinement_partition (e p q : R) :
    (1 - e) + e * sector p q (false, false) + e * sector p q (false, true) +
      e * sector p q (true, false) + e * sector p q (true, true) = 1 := by
  simp only [sector, part]
  noncomm_ring

lemma commute_sector {e p q : R} (hp : Commute e p) (hq : Commute e q)
    (i : Bool × Bool) : Commute e (sector p q i) := by
  have hp' : Commute e (part p i.1) := by
    cases i.1 <;> (show e * part p _ = part p _ * e; simp only [part]; noncomm_ring [hp.eq])
  have hq' : Commute e (part q i.2) := by
    cases i.2 <;> (show e * part q _ = part q _ * e; simp only [part]; noncomm_ring [hq.eq])
  exact hp'.mul_right hq'

/-- A sufficient compatibility condition for an orthogonal ambient refinement. -/
theorem refinement_isStarProjection [StarRing R] {e p q : R}
    (he : IsStarProjection e) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : Commute p q) (hep : Commute e p) (heq : Commute e q)
    (i : Bool × Bool) : IsStarProjection (e * sector p q i) :=
  he.mul (sector_isStarProjection hp hq hpq i) (commute_sector hep heq i)

end InfoGeometry.Singular.MoorePenroseSectors

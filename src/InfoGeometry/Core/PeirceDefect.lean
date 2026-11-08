/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotencyDefect
import InfoGeometry.Core.PeirceQuadraticFrame

/-!
# The idempotency defect along Peirce tangent directions

The algebraic linearization at an idempotent is `y ↦ p*y+y*p-y`.
Its vanishing is equivalent to both diagonal corners vanishing. Along this
tangent subspace the shifted defect is exactly the square, which belongs to
the centralizer of the original idempotent. No division is used.
-/

namespace InfoGeometry.Core.PeirceDefect

open IdempotencyDefect PeirceDecomposition PeirceGrading
open PeirceCoupledCorners PeirceQuadraticFrame

variable {A : Type*} [Ring A] {p y u v : A}

theorem defect_add_idempotent (hp : IsIdempotentElem p) (y : A) :
    defect (p + y) = y * y + (p * y + y * p - y) := by
  unfold defect
  noncomm_ring [hp.eq]

/-- Exact algebraic tangent criterion, valid also in characteristic two. -/
theorem defect_add_idempotent_eq_square_iff (hp : IsIdempotentElem p) :
    defect (p + y) = y * y ↔ p * y + y * p = y := by
  rw [defect_add_idempotent hp]
  constructor
  · intro h
    have hz : p * y + y * p - y = 0 :=
      add_left_cancel (h.trans (add_zero (y * y)).symm)
    exact sub_eq_zero.mp hz
  · intro h
    rw [h, sub_self, add_zero]

theorem defect_add_idempotent_eq_square (hp : IsIdempotentElem p)
    (hy : p * y + y * p = y) : defect (p + y) = y * y :=
  (defect_add_idempotent_eq_square_iff hp).2 hy

/-- The algebraic linearization kernel consists exactly of the two mixed Peirce corners. -/
theorem tangent_iff_diagonal_corners_zero (hp : IsIdempotentElem p) :
    p * y + y * p = y ↔ component11 p y = 0 ∧ component00 p y = 0 := by
  constructor
  · intro hy
    have h11 : p * y * p = 0 := by
      have h := congrArg (fun z => p * z) hy
      rw [mul_add, ← mul_assoc p p y, hp.eq, ← mul_assoc p y p] at h
      exact add_left_cancel (h.trans (add_zero (p * y)).symm)
    refine ⟨h11, ?_⟩
    change (1 - p) * y * (1 - p) = 0
    calc
      _ = y - (p * y + y * p) + p * y * p := by noncomm_ring
      _ = 0 := by rw [hy, h11]; simp
  · rintro ⟨h11, h00⟩
    have he : even p y = 0 := by
      change component11 p y + component00 p y = 0
      rw [h11, h00, add_zero]
    have ho : odd p y = y := by
      have h := even_add_odd p y
      rwa [he, zero_add] at h
    exact (mem_odd_iff hp).1 ⟨y, ho⟩

/-- The tangent equation reconstructs the element from its two directed mixed corners. -/
theorem tangent_iff_mixed_corners (hp : IsIdempotentElem p) :
    p * y + y * p = y ↔ y = component10 p y + component01 p y := by
  rw [← mem_odd_iff hp,
    LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent hp), odd_apply]
  exact eq_comm

/-- A tangent square lies in the even subalgebra, hence commutes with the base point. -/
theorem commute_square_of_tangent (hp : IsIdempotentElem p)
    (hy : p * y + y * p = y) : Commute p (y * y) := by
  have ho := (mem_odd_iff hp).2 hy
  exact (mem_even_iff hp).1 (odd_mul_odd hp ho ho)

theorem defect_add_commutator (hp : IsIdempotentElem p) (x : A) :
    defect (p + (p * x - x * p)) = (p * x - x * p) * (p * x - x * p) :=
  defect_add_idempotent_eq_square hp ((mem_odd_iff hp).1 (commutator_odd hp x))

theorem defect_add_odd (hp : IsIdempotentElem p) (x : A) :
    defect (p + odd p x) = odd p x * odd p x :=
  defect_add_idempotent_eq_square hp ((mem_odd_iff hp).1 ⟨x, rfl⟩)

theorem defect_add_mem10 (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    defect (p + u) = 0 := by
  have hu2 := peirce10_mul_peirce10_eq_zero p hp.eq hu hu
  unfold defect
  noncomm_ring [hp.eq, left_support10 hp hu, right_support10 hp hu, hu2]

theorem defect_add_mem01 (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    defect (p + v) = 0 := by
  have hv2 := peirce01_mul_peirce01_eq_zero p hp.eq hv hv
  unfold defect
  noncomm_ring [hp.eq, left_support01 hp hv, right_support01 hp hv, hv2]

theorem defect_add_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    defect (p + (u + v)) = u * v + v * u := by
  rw [defect_add_idempotent_eq_square hp
    ((mem_odd_iff hp).1 (coupled_odd hp hu hv)), ← pow_two]
  exact coupled_square hp hu hv

theorem defect_add_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    defect (p + (u - v)) = -(u * v + v * u) := by
  have hy : p * (u - v) + (u - v) * p = u - v := by
    rw [mul_sub, sub_mul, left_support10 hp hu, left_support01 hp hv,
      right_support10 hp hu, right_support01 hp hv]
    abel
  rw [defect_add_idempotent_eq_square hp hy, ← pow_two]
  exact difference_square hp hu hv

end InfoGeometry.Core.PeirceDefect

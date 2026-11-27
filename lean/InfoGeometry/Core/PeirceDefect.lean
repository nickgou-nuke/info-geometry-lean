/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotencyDefect
import InfoGeometry.Core.ParabolicShearRelations
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

/-- A commutator tangent has a square defect, and that square lies in the
centralizer of the idempotent. This records both consequences of the tangent
criterion rather than only restating its forward implication. -/
theorem commutator_tangent_defect_and_centrality (hp : IsIdempotentElem p) (x : A) :
    defect (p + (p * x - x * p)) = (p * x - x * p) * (p * x - x * p) ∧
    Commute p ((p * x - x * p) * (p * x - x * p)) := by
  have ht : p * (p * x - x * p) + (p * x - x * p) * p = p * x - x * p :=
    (mem_odd_iff hp).1 (commutator_odd hp x)
  exact ⟨(defect_add_idempotent_eq_square_iff hp).2 ht,
    commute_square_of_tangent hp ht⟩

/-- The canonical odd Peirce component has a square defect whose value
centralizes the base idempotent. -/
theorem odd_tangent_defect_and_centrality (hp : IsIdempotentElem p) (x : A) :
    defect (p + odd p x) = odd p x * odd p x ∧
    Commute p (odd p x * odd p x) := by
  have ht : p * odd p x + odd p x * p = odd p x :=
    (mem_odd_iff hp).1 ⟨x, rfl⟩
  exact ⟨(defect_add_idempotent_eq_square_iff hp).2 ht,
    commute_square_of_tangent hp ht⟩

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
  rw [(defect_add_idempotent_eq_square_iff hp).2
    ((mem_odd_iff hp).1 (coupled_odd hp hu hv)), ← pow_two]
  exact coupled_square hp hu hv

theorem defect_add_difference (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    defect (p + (u - v)) = -(u * v + v * u) := by
  have hy : p * (u - v) + (u - v) * p = u - v := by
    rw [mul_sub, sub_mul, left_support10 hp hu, left_support01 hp hv,
      right_support10 hp hu, right_support01 hp hv]
    abel
  rw [(defect_add_idempotent_eq_square_iff hp).2 hy, ← pow_two]
  exact difference_square hp hu hv

/-! ## Square-zero tangent and commuting perturbations -/

open ParabolicShearRelations

variable {n : A}

/-- A square-zero perturbation preserves idempotence exactly on the
algebraic Peirce tangent space. Nonzero perturbation alone does not imply
nonzero defect. -/
theorem defect_add_square_zero_eq_zero_iff
    (hp : IsIdempotentElem p) (hn : n * n = 0) :
    defect (p + n) = 0 ↔ p * n + n * p = n := by
  simpa only [hn] using (defect_add_idempotent_eq_square_iff (y := n) hp)

/-- The native idempotent predicate has the same exact tangent criterion. -/
theorem isIdempotentElem_add_square_zero_iff
    (hp : IsIdempotentElem p) (hn : n * n = 0) :
    IsIdempotentElem (p + n) ↔ p * n + n * p = n := by
  rw [← defect_eq_zero_iff]
  exact defect_add_square_zero_eq_zero_iff hp hn

/-- In the commuting regime the defect is multiplication by the native
Peirce reflection `2 * p - 1`; no commutativity of the ambient ring is used. -/
theorem defect_add_square_zero_of_commute
    (hp : IsIdempotentElem p) (hn : n * n = 0) (hpn : Commute p n) :
    defect (p + n) = reflection p * n := by
  rw [defect_add_idempotent hp, hn, zero_add, ← hpn.eq]
  unfold reflection
  noncomm_ring

/-- A square-zero perturbation commuting with the idempotent produces a
square-zero defect. The commutation hypothesis cannot be omitted. -/
theorem defect_add_square_zero_mul_self_of_commute
    (hp : IsIdempotentElem p) (hn : n * n = 0) (hpn : Commute p n) :
    defect (p + n) * defect (p + n) = 0 := by
  rw [defect_add_square_zero_of_commute hp hn hpn]
  have href : Commute (reflection p) n :=
    even_commutes_reflection hp ((mem_even_iff hp).2 hpn.eq)
  calc
    (reflection p * n) * (reflection p * n) = (reflection p * n) ^ 2 :=
      (pow_two _).symm
    _ = (reflection p) ^ 2 * n ^ 2 := href.mul_pow 2
    _ = 0 := by simp only [pow_two, reflection_sq hp, hn, mul_zero]

/-- The native reflection is invertible, so in the commuting regime
the defect vanishes exactly when the square-zero perturbation vanishes. -/
theorem defect_add_square_zero_eq_zero_iff_of_commute
    (hp : IsIdempotentElem p) (hn : n * n = 0) (hpn : Commute p n) :
    defect (p + n) = 0 ↔ n = 0 := by
  rw [defect_add_square_zero_of_commute hp hn hpn]
  constructor
  · intro hzero
    calc
      n = (reflection p * reflection p) * n := by
        rw [reflection_sq hp, one_mul]
      _ = reflection p * (reflection p * n) := mul_assoc _ _ _
      _ = 0 := by rw [hzero, mul_zero]
  · rintro rfl
    exact mul_zero _

/-- Nonzero commuting square-zero perturbations cannot be tangent to the
idempotent locus. This is the precise incompatibility between the two regimes. -/
theorem tangent_square_zero_eq_zero_of_commute
    (hp : IsIdempotentElem p) (hn : n * n = 0) (hpn : Commute p n)
    (ht : p * n + n * p = n) : n = 0 := by
  exact (defect_add_square_zero_eq_zero_iff_of_commute hp hn hpn).1
    ((defect_add_square_zero_eq_zero_iff hp hn).2 ht)

/-- A one-sided shear of the projector is an actual unit conjugation.
The two support equations fix the orientation of the conjugating shear. -/
theorem add_eq_shear_conjugate_of_support
    (hn : n * n = 0) (hleft : p * n = n) (hright : n * p = 0) :
    p + n =
      (((shearUnit n hn)⁻¹ : Aˣ) : A) * p * (shearUnit n hn : A) := by
  change p + n = (1 - n) * p * (1 + n)
  calc
    p + n = p + p * n - n * p - (n * p) * n := by
      rw [hleft, hright]
      simp only [zero_mul, sub_zero]
    _ = (1 - n) * p * (1 + n) := by noncomm_ring

end InfoGeometry.Core.PeirceDefect

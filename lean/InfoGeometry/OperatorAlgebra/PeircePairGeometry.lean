/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceChiralGeometry

/-!
# Opposite Peirce corners in the full complex matrix algebra

The two inputs are independent. Their directed corners have an even mixed
square, and reflection interchanges the ordered Jordan sum and Lie bracket.
Nonvanishing is characterized by noncommutation; it is not assumed or automatic.
The existing Peirce operations and reflection are used without new wrappers.
-/

namespace InfoGeometry.OperatorAlgebra.PeircePairGeometry

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan
open PeirceChiralGeometry MatrixTraceGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p : Matrix n n ℂ}

/-- The square of a sum of independently chosen opposite corners. -/
theorem pair_square (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    ((component10 p A) + (component01 p B)) * ((component10 p A) + (component01 p B)) = (component10 p A) * (component01 p B) + (component01 p B) * (component10 p A) := by
  have hu := (corners_square_zero hp.eq A).1
  have hv := (corners_square_zero hp.eq B).2
  noncomm_ring [hu, hv]

/-- The two inputs reconstruct an element in the actual odd Peirce image. -/
theorem oddPart_pair (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    oddPart p ((component10 p A) + (component01 p B)) = (component10 p A) + (component01 p B) := by
  simp only [oddPart, component10, component01, complementIdempotent]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem reflection_pair (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    reflection p * ((component10 p A) + (component01 p B)) * reflection p = -((component10 p A) + (component01 p B)) := by
  have h := (conjugation_on_parts hp.eq ((component10 p A) + (component01 p B))).2
  rwa [oddPart_pair hp A B] at h

theorem reflection_pair_anticommute (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    reflection p * ((component10 p A) + (component01 p B)) + ((component10 p A) + (component01 p B)) * reflection p = 0 :=
  (oddPart_eq_self_iff_reflection_anticommute hp _).mp (oddPart_pair hp A B)

/-- The first projection extracts the forward corner by left action. -/
theorem idempotent_mul_pair_sum (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    p * ((component10 p A) + (component01 p B)) = (component10 p A) := by
  simp only [component10, component01, complementIdempotent]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- The complementary projection extracts the reverse corner. -/
theorem complement_mul_pair_sum (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    (1 - p) * ((component10 p A) + (component01 p B)) = (component01 p B) := by
  simp only [component10, component01, complementIdempotent]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem pair_sum_eq_zero_iff (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    (component10 p A) + (component01 p B) = 0 ↔ (component10 p A) = 0 ∧ (component01 p B) = 0 := by
  constructor
  · intro h
    constructor
    · rw [← idempotent_mul_pair_sum hp A B, h, mul_zero]
    · rw [← complement_mul_pair_sum hp A B, h, mul_zero]
  · rintro ⟨hu, hv⟩
    rw [hu, hv, add_zero]

/-- The exact kernel splits into the kernels of the two directed actions. -/
theorem pair_sum_mulVec_eq_zero_iff (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) (v : n → ℂ) :
    ((component10 p A) + (component01 p B)) *ᵥ v = 0 ↔ (component10 p A) *ᵥ v = 0 ∧ (component01 p B) *ᵥ v = 0 := by
  constructor
  · intro h
    constructor
    · rw [← idempotent_mul_pair_sum hp A B, ← mulVec_mulVec, h, mulVec_zero]
    · rw [← complement_mul_pair_sum hp A B, ← mulVec_mulVec, h, mulVec_zero]
  · rintro ⟨hu, hv⟩
    rw [add_mulVec, hu, hv, add_zero]

/-- The reflection converts the ordered Jordan sum into the native Lie bracket. -/
theorem reflection_mul_pair_jordan (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    reflection p * ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) = ⁅(component10 p A), (component01 p B)⁆ := by
  simp only [reflection, two_nsmul, component10, component01,
    complementIdempotent, Ring.lie_def]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- The reverse conversion follows from the already-owned involution law. -/
theorem reflection_mul_pair_lie (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    reflection p * ⁅(component10 p A), (component01 p B)⁆ = (component10 p A) * (component01 p B) + (component01 p B) * (component10 p A) := by
  rw [← reflection_mul_pair_jordan hp A B, ← mul_assoc, reflection_sq hp.eq, one_mul]

theorem pair_jordan_eq_zero_iff_lie (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    (component10 p A) * (component01 p B) + (component01 p B) * (component10 p A) = 0 ↔ ⁅(component10 p A), (component01 p B)⁆ = 0 := by
  constructor
  · intro h
    rw [← reflection_mul_pair_jordan hp A B, h, mul_zero]
  · intro h
    rw [← reflection_mul_pair_lie hp A B, h, mul_zero]

/-- No commuting hypothesis: noncommutation is exactly the nonvanishing criterion. -/
theorem pair_jordan_ne_zero_iff_not_commute (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    (component10 p A) * (component01 p B) + (component01 p B) * (component10 p A) ≠ 0 ↔ ¬ Commute (component10 p A) (component01 p B) := by
  rw [ne_eq, pair_jordan_eq_zero_iff_lie hp A B, Ring.lie_def, sub_eq_zero]
  rfl

/-- The even square commutes with the projection, not necessarily with the ambient algebra. -/
theorem commute_pair_jordan (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    Commute p ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) := by
  have h := commute_odd_square hp ((component10 p A) + (component01 p B))
  rwa [oddPart_pair hp A B, pair_square hp A B] at h

theorem commute_pair_lie (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    Commute p ⁅(component10 p A), (component01 p B)⁆ := by
  change p * ⁅(component10 p A), (component01 p B)⁆ = ⁅(component10 p A), (component01 p B)⁆ * p
  simp only [Ring.lie_def, component10, component01, complementIdempotent]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- Conjugation preserves the mixed square by multiplicativity of the native ring equivalence. -/
theorem reflection_conj_pair_jordan (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    reflection p * ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) * reflection p = (component10 p A) * (component01 p B) + (component01 p B) * (component10 p A) := by
  have h := (reflectionConj p hp.eq).map_mul ((component10 p A) + (component01 p B)) ((component10 p A) + (component01 p B))
  change reflection p * (((component10 p A) + (component01 p B)) * ((component10 p A) + (component01 p B))) * reflection p =
    (reflection p * ((component10 p A) + (component01 p B)) * reflection p) *
      (reflection p * ((component10 p A) + (component01 p B)) * reflection p) at h
  rwa [pair_square hp A B, reflection_pair hp A B, neg_mul_neg,
    pair_square hp A B] at h

theorem commute_reflection_pair_jordan (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    Commute (reflection p) ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) := by
  change reflection p * _ = _ * reflection p
  have h := congrArg (fun X => X * reflection p) (reflection_conj_pair_jordan hp A B)
  simpa only [mul_assoc, reflection_sq hp.eq, mul_one] using h

theorem reflection_conj_pair_lie (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    reflection p * ⁅(component10 p A), (component01 p B)⁆ * reflection p = ⁅(component10 p A), (component01 p B)⁆ := by
  rw [← reflection_mul_pair_jordan hp A B]
  calc
    _ = (reflection p * reflection p) * ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) * reflection p := by
      simp only [mul_assoc]
    _ = ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) * reflection p := by rw [reflection_sq hp.eq, one_mul]
    _ = reflection p * ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) :=
      (commute_reflection_pair_jordan hp A B).eq.symm

theorem commute_reflection_pair_lie (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) : Commute (reflection p) ⁅(component10 p A), (component01 p B)⁆ := by
  change reflection p * _ = _ * reflection p
  have h := congrArg (fun X => X * reflection p) (reflection_conj_pair_lie hp A B)
  simpa only [mul_assoc, reflection_sq hp.eq, mul_one] using h

theorem component11_pair_jordan (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    component11 p ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) = (component10 p A) * (component01 p B) := by
  simp only [component11, component10, component01, complementIdempotent]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem component00_pair_jordan (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    component00 p ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) = (component01 p B) * (component10 p A) := by
  simp only [component00, component10, component01, complementIdempotent]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem component11_pair_lie (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    component11 p ⁅(component10 p A), (component01 p B)⁆ = (component10 p A) * (component01 p B) := by
  simp only [component11, component10, component01, complementIdempotent, Ring.lie_def]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem component00_pair_lie (hp : IsIdempotentElem p) (A B : Matrix n n ℂ) :
    component00 p ⁅(component10 p A), (component01 p B)⁆ = -((component01 p B) * (component10 p A)) := by
  simp only [component00, component10, component01, complementIdempotent, Ring.lie_def]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- Distinct corners cannot cancel; no characteristic-zero argument is needed. -/
theorem pair_jordan_eq_zero_iff_products (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    (component10 p A) * (component01 p B) + (component01 p B) * (component10 p A) = 0 ↔ (component10 p A) * (component01 p B) = 0 ∧ (component01 p B) * (component10 p A) = 0 := by
  constructor
  · intro h
    constructor
    · rw [← component11_pair_jordan hp A B, h]
      simp [component11]
    · rw [← component00_pair_jordan hp A B, h]
      simp [component00]
  · rintro ⟨huv, hvu⟩
    rw [huv, hvu, add_zero]

/-- Cyclic trace, independent of idempotence or any adjoint relation. -/
theorem trace_pair_jordan (p A B : Matrix n n ℂ) :
    trace ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A)) = (2 : ℂ) * trace ((component10 p A) * (component01 p B)) := by
  rw [trace_add, trace_mul_comm (component01 p B) (component10 p A), two_mul]

theorem trace_pair_jordan_corners (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    trace (component11 p ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A))) =
      trace (component00 p ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A))) := by
  rw [component11_pair_jordan hp A B, component00_pair_jordan hp A B]
  exact trace_mul_comm (component10 p A) (component01 p B)

theorem trace_pair_lie_corners (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    trace (component11 p ⁅(component10 p A), (component01 p B)⁆) + trace (component00 p ⁅(component10 p A), (component01 p B)⁆) = 0 := by
  rw [component11_pair_lie hp A B, component00_pair_lie hp A B, trace_neg,
    trace_mul_comm (component01 p B) (component10 p A), add_neg_cancel]

theorem trace_reflection_pair_lie (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    trace (reflection p * ⁅(component10 p A), (component01 p B)⁆) = (2 : ℂ) * trace ((component10 p A) * (component01 p B)) := by
  rw [reflection_mul_pair_lie hp A B, trace_pair_jordan]

theorem trace_reflection_pair_jordan (hp : IsIdempotentElem p)
    (A B : Matrix n n ℂ) :
    trace (reflection p * ((component10 p A) * (component01 p B) + (component01 p B) * (component10 p A))) = 0 := by
  rw [reflection_mul_pair_jordan hp A B]
  exact trace_lie_zero (component10 p A) (component01 p B)

end InfoGeometry.OperatorAlgebra.PeircePairGeometry

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceDecomposition
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Division-free Peirce grading

Contract: for an idempotent in an arbitrary associative ring, the diagonal and
cross-corner maps are complementary `ℤ`-linear projections. They give an actual
internal direct sum, including in characteristic two. Identification with the
full reflection eigenspaces requires injectivity of doubling. This is an
algebraic symmetric decomposition, not a positivity-based Cartan involution.
The four corners are owned by `PeirceDecomposition`; no new carrier is introduced.
-/

namespace InfoGeometry.Core.PeirceGrading

open PeirceDecomposition

variable {A : Type*} [Ring A]

/-- Diagonal Peirce projection as a native linear endomorphism. -/
def even (p : A) : A →ₗ[ℤ] A :=
  ({ toFun := fun x => component11 p x + component00 p x
     map_zero' := by simp [component11, component00]
     map_add' := fun x y => by
       simp only [component11, component00, mul_add, add_mul]
       abel } : A →+ A).toIntLinearMap

/-- Complementary off-diagonal projection. -/
def odd (p : A) : A →ₗ[ℤ] A := LinearMap.id - even p

/-- Reflection associated to the given idempotent. -/
def reflection (p : A) : A := 2 * p - 1

@[simp] theorem even_apply (p x : A) :
    even p x = p * x * p + (1 - p) * x * (1 - p) := rfl

@[simp] theorem odd_apply (p x : A) :
    odd p x = p * x * (1 - p) + (1 - p) * x * p := by
  simp only [odd, LinearMap.sub_apply, LinearMap.id_apply, even_apply]
  noncomm_ring

theorem even_add_odd (p x : A) : even p x + odd p x = x := by
  simp [odd]

theorem even_idempotent {p : A} (hp : IsIdempotentElem p) :
    IsIdempotentElem (even p) := by
  ext x
  change even p (even p x) = even p x
  simp only [even_apply]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem odd_idempotent {p : A} (hp : IsIdempotentElem p) :
    IsIdempotentElem (odd p) := (even_idempotent hp).one_sub

/-- The genuine internal direct sum holds without cancellation of two. -/
theorem isCompl {p : A} (hp : IsIdempotentElem p) :
    IsCompl (LinearMap.range (even p)) (LinearMap.range (odd p)) := by
  rw [show LinearMap.range (odd p) = LinearMap.ker (even p) from
    (LinearMap.IsIdempotentElem.ker_eq_range (even_idempotent hp)).symm]
  exact LinearMap.IsIdempotentElem.isCompl (even_idempotent hp)

/-- Explicit native linear equivalence realizing the direct sum. -/
noncomputable def decomposition {p : A} (hp : IsIdempotentElem p) :
    A ≃ₗ[ℤ] LinearMap.range (even p) × LinearMap.range (odd p) :=
  (Submodule.prodEquivOfIsCompl _ _ (isCompl hp)).symm

theorem mem_even_iff {p x : A} (hp : IsIdempotentElem p) :
    x ∈ LinearMap.range (even p) ↔ p * x = x * p := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (even_idempotent hp)]
  constructor
  · intro h
    rw [← h]
    simp only [even_apply]
    noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]
  · intro h
    simp only [even_apply]
    have hx : p * x * p = x * p := by rw [h, mul_assoc, hp.eq]
    noncomm_ring [h, hx, hp.eq]

theorem mem_odd_iff {p x : A} (hp : IsIdempotentElem p) :
    x ∈ LinearMap.range (odd p) ↔ p * x + x * p = x := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent hp)]
  constructor
  · intro h
    rw [← h]
    simp only [odd_apply]
    noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]
  · intro h
    have hx : p * x * p = 0 := by
      have hh := congrArg (fun y => p * y) h
      rw [mul_add, ← mul_assoc p p x, hp.eq, ← mul_assoc p x p] at hh
      exact add_left_cancel (hh.trans (add_zero (p * x)).symm)
    simp only [odd_apply]
    calc
      _ = p * x + x * p - (p * x * p + p * x * p) := by noncomm_ring
      _ = x := by rw [h, hx]; simp

theorem reflection_sq {p : A} (hp : IsIdempotentElem p) :
    reflection p * reflection p = 1 := by
  unfold reflection
  noncomm_ring [hp.eq]

/-- The reflection acts by opposite signs on the two complementary supports. -/
theorem reflection_support_actions {p : A} (hp : IsIdempotentElem p) :
    reflection p * p = p ∧ reflection p * (1 - p) = -(1 - p) := by
  unfold reflection
  constructor <;> noncomm_ring [hp.eq]

theorem conjugate_eq (p x : A) :
    reflection p * x * reflection p = even p x - odd p x := by
  simp only [reflection, even_apply, odd_apply]
  noncomm_ring

theorem scaled_parts (p x : A) :
    x + reflection p * x * reflection p = 2 • even p x ∧
    x - reflection p * x * reflection p = 2 • odd p x := by
  rw [conjugate_eq, two_nsmul, two_nsmul]
  constructor <;> (nth_rw 1 [← even_add_odd p x]; abel)

theorem reflection_commutator (p x : A) :
    reflection p * x - x * reflection p = 2 • (p * x - x * p) := by
  simp only [reflection, two_nsmul]
  noncomm_ring

theorem reflection_anticommutator (p x : A) :
    reflection p * x + x * reflection p = 2 • (p * x + x * p - x) := by
  simp only [reflection, two_nsmul]
  noncomm_ring

/-- Only the eigenspace identification needs a two-torsion restriction. -/
theorem eigenspace_criteria {p x : A} (hp : IsIdempotentElem p)
    (h2 : Function.Injective (fun y : A => (2 : ℕ) • y)) :
    (x ∈ LinearMap.range (even p) ↔ reflection p * x = x * reflection p) ∧
    (x ∈ LinearMap.range (odd p) ↔ reflection p * x + x * reflection p = 0) := by
  have cancel (y : A) : 2 • y = 0 ↔ y = 0 := by
    constructor
    · intro h; exact h2 (by simpa using h)
    · rintro rfl; simp
  rw [mem_even_iff hp, mem_odd_iff hp, ← sub_eq_zero (a := reflection p * x),
    reflection_commutator, reflection_anticommutator, cancel, cancel,
    sub_eq_zero, sub_eq_zero]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- Reflection conjugation on the actual ambient ring, as a native endomorphism. -/
def conjugation (p : A) : Module.End ℤ A := even p - odd p

@[simp] theorem conjugation_apply (p x : A) :
    conjugation p x = reflection p * x * reflection p := (conjugate_eq p x).symm

/-- Identification with the full native eigenspaces, under precisely the
cancellation used in the proof. Inverting two is not necessary. -/
theorem eigenspaces {p : A} (hp : IsIdempotentElem p)
    (h2 : Function.Injective (fun y : A => (2 : ℕ) • y)) :
    (conjugation p).eigenspace 1 = LinearMap.range (even p) ∧
    (conjugation p).eigenspace (-1) = LinearMap.range (odd p) := by
  have hsq := reflection_sq hp
  have heq (x : A) : reflection p * x * reflection p = x ↔
      reflection p * x = x * reflection p := by
    constructor
    · intro h
      have hh := congrArg (fun y => y * reflection p) h
      simpa only [mul_assoc, hsq, mul_one] using hh
    · intro h
      rw [h, mul_assoc, hsq, mul_one]
  have hneg (x : A) : reflection p * x * reflection p = -x ↔
      reflection p * x + x * reflection p = 0 := by
    constructor
    · intro h
      have hh := congrArg (fun y => y * reflection p) h
      simp only [mul_assoc, hsq, mul_one, neg_mul] at hh
      rw [hh, neg_add_cancel]
    · intro h
      rw [eq_neg_of_add_eq_zero_left h, neg_mul, mul_assoc, hsq, mul_one]
  constructor <;> ext x
  · rw [Module.End.mem_eigenspace_iff, conjugation_apply, one_smul,
      heq, ← (eigenspace_criteria hp h2).1]
  · rw [Module.End.mem_eigenspace_iff, conjugation_apply, neg_one_smul,
      hneg, ← (eigenspace_criteria hp h2).2]

/-- An idempotent commutator is odd without any restriction on two. -/
theorem commutator_odd {p : A} (hp : IsIdempotentElem p) (x : A) :
    p * x - x * p ∈ LinearMap.range (odd p) := by
  rw [mem_odd_iff hp]
  noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

theorem odd_reconstruction {p : A} (hp : IsIdempotentElem p) (x : A) :
    odd p x = reflection p * (p * x - x * p) ∧
    odd p x = p * (p * x - x * p) - (p * x - x * p) * p := by
  simp only [odd_apply, reflection]
  constructor <;> noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]

/-- Each directed corner, not their sum in general, is square-zero. -/
theorem corners_sq_zero {p : A} (hp : IsIdempotentElem p) (x : A) :
    (p * x * (1 - p)) ^ 2 = 0 ∧ ((1 - p) * x * p) ^ 2 = 0 := by
  constructor
  · calc
      _ = p * x * ((1 - p) * p) * x * (1 - p) := by noncomm_ring
      _ = 0 := by rw [hp.one_sub_mul_self]; simp
  · calc
      _ = (1 - p) * x * (p * (1 - p)) * x * p := by noncomm_ring
      _ = 0 := by rw [hp.mul_one_sub_self]; simp

/-- Even elements form an associative subalgebra (here expressed by membership). -/
theorem even_mul_even {p x y : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (even p)) (hy : y ∈ LinearMap.range (even p)) :
    x * y ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp] at hx hy ⊢
  exact (show Commute p x from hx).mul_right hy

theorem even_mul_odd {p x y : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (even p)) (hy : y ∈ LinearMap.range (odd p)) :
    x * y ∈ LinearMap.range (odd p) := by
  rw [mem_even_iff hp] at hx
  rw [mem_odd_iff hp] at hy ⊢
  calc
    _ = (p * x) * y + x * (y * p) := by noncomm_ring
    _ = x * (p * y + y * p) := by rw [hx]; noncomm_ring
    _ = x * y := by rw [hy]

theorem odd_mul_even {p x y : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (odd p)) (hy : y ∈ LinearMap.range (even p)) :
    x * y ∈ LinearMap.range (odd p) := by
  rw [mem_even_iff hp] at hy
  rw [mem_odd_iff hp] at hx ⊢
  calc
    _ = (p * x) * y + x * (y * p) := by noncomm_ring
    _ = (p * x + x * p) * y := by rw [← hy]; noncomm_ring
    _ = x * y := by rw [hx]

theorem odd_mul_odd {p x y : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (odd p)) (hy : y ∈ LinearMap.range (odd p)) :
    x * y ∈ LinearMap.range (even p) := by
  rw [mem_odd_iff hp] at hx hy
  rw [mem_even_iff hp]
  have hx' := eq_sub_of_add_eq hx
  have hy' := eq_sub_of_add_eq hy
  calc
    p * (x * y) = (p * x) * y := (mul_assoc _ _ _).symm
    _ = x * y - x * (p * y) := by rw [hx']; noncomm_ring
    _ = x * y * p := by rw [hy']; noncomm_ring

/-- Native Lie brackets obey the three symmetric-decomposition routing laws. -/
theorem lie_routing {p : A} (hp : IsIdempotentElem p) :
    (∀ x ∈ LinearMap.range (even p), ∀ y ∈ LinearMap.range (even p),
      ⁅x, y⁆ ∈ LinearMap.range (even p)) ∧
    (∀ x ∈ LinearMap.range (odd p), ∀ y ∈ LinearMap.range (odd p),
      ⁅x, y⁆ ∈ LinearMap.range (even p)) ∧
    (∀ x ∈ LinearMap.range (even p), ∀ y ∈ LinearMap.range (odd p),
      ⁅x, y⁆ ∈ LinearMap.range (odd p)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    exact (LinearMap.range (even p)).sub_mem (even_mul_even hp hx hy) (even_mul_even hp hy hx)
  · intro x hx y hy
    exact (LinearMap.range (even p)).sub_mem (odd_mul_odd hp hx hy) (odd_mul_odd hp hy hx)
  · intro x hx y hy
    exact (LinearMap.range (odd p)).sub_mem (even_mul_odd hp hx hy) (odd_mul_even hp hy hx)

theorem even_commutes_reflection {p x : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (even p)) : Commute (reflection p) x := by
  apply sub_eq_zero.mp
  rw [reflection_commutator, (mem_even_iff hp).mp hx, sub_self, smul_zero]

theorem odd_anticommutes_reflection {p x : A} (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (odd p)) : reflection p * x + x * reflection p = 0 := by
  rw [reflection_anticommutator, (mem_odd_iff hp).mp hx, sub_self, smul_zero]

section Star
variable [StarRing A]

theorem reflection_star {p : A} (hp : IsSelfAdjoint p) :
    IsSelfAdjoint (reflection p) := by
  change star (2 * p - 1) = 2 * p - 1
  simp [hp.star_eq, two_mul]

/-- A self-adjoint idempotent gives a native unitary reflection. -/
theorem reflection_mem_unitary {p : A} (hp : IsStarProjection p) :
    reflection p ∈ unitary A := by
  constructor <;> rw [(reflection_star hp.isSelfAdjoint).star_eq,
    reflection_sq hp.isIdempotentElem]

end Star
end InfoGeometry.Core.PeirceGrading

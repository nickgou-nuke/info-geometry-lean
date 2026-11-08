/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceQuadraticFrame
import Mathlib.Algebra.Lie.OfAssociative

/-!
# All-order inner action on an opposite-corner quadratic frame

Composition powers are native `Module.End` powers. The weight remains an
operator of the ambient algebra, never a scalar frequency. The generated
invariant submodule is a span, not a claimed basis or two-dimensional space.
-/

namespace InfoGeometry.Core.PeirceQuadraticIteration
attribute [local instance 100] LieRing.ofAssociativeRing
open PeirceDecomposition PeirceQuadraticFrame
variable (R : Type*) [CommRing R] {A : Type*} [Ring A] [Algebra R A]

/-- A commuting left factor passes through the actual inner derivation. -/
theorem ad_mul_left {c t : A} (ht : Commute c t) (x : A) :
    LieAlgebra.ad R A c (t * x) = t * LieAlgebra.ad R A c x := by
  change c * (t * x) - (t * x) * c = t * (c * x - x * c)
  rw [← mul_assoc c t x, ht.eq]
  noncomm_ring

/-- The same transport holds for every composition power. -/
theorem ad_pow_mul_left {c t : A} (ht : Commute c t) (n : ℕ) (x : A) :
    (LieAlgebra.ad R A c ^ n) (t * x) =
      t * (LieAlgebra.ad R A c ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [ih, ad_mul_left R ht]

/-- A second-step relation propagates with the full operator weight. -/
theorem ad_pow_even_of_square {c t x : A} (ht : Commute c t)
    (hx : (LieAlgebra.ad R A c ^ 2) x = t ^ 2 * x) (n : ℕ) :
    (LieAlgebra.ad R A c ^ (2 * n)) x = t ^ (2 * n) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ]
    calc
      (LieAlgebra.ad R A c ^ (2 * n + 2)) x =
          t ^ 2 * (t ^ (2 * n) * x) := by
        rw [pow_add, Module.End.mul_apply, hx,
          ad_pow_mul_left R (ht.pow_right 2), ih]
      _ = t ^ (2 * n + 2) * x := by
        rw [← mul_assoc, ← pow_add, Nat.add_comm 2 (2 * n)]

/-- The square relation follows from the two first-step equations. -/
theorem ad_square_of_reciprocal {c t e j : A} (ht : Commute c t)
    (he : LieAlgebra.ad R A c e = t * j)
    (hj : LieAlgebra.ad R A c j = t * e) :
    (LieAlgebra.ad R A c ^ 2) e = t ^ 2 * e := by
  rw [pow_two, Module.End.mul_apply, he, ad_mul_left R ht, hj, pow_two, mul_assoc]

/-- Even powers return the first member with its operator weight. -/
theorem ad_pow_even_of_reciprocal {c t e j : A} (ht : Commute c t)
    (he : LieAlgebra.ad R A c e = t * j)
    (hj : LieAlgebra.ad R A c j = t * e) (n : ℕ) :
    (LieAlgebra.ad R A c ^ (2 * n)) e = t ^ (2 * n) * e :=
  ad_pow_even_of_square R ht (ad_square_of_reciprocal R ht he hj) n

/-- Odd powers exchange the members with their operator weight. -/
theorem ad_pow_odd_of_reciprocal {c t e j : A} (ht : Commute c t)
    (he : LieAlgebra.ad R A c e = t * j)
    (hj : LieAlgebra.ad R A c j = t * e) (n : ℕ) :
    (LieAlgebra.ad R A c ^ (2 * n + 1)) e = t ^ (2 * n + 1) * j := by
  rw [pow_succ', Module.End.mul_apply, ad_pow_even_of_reciprocal R ht he hj,
    ad_mul_left R (ht.pow_right (2 * n)), he, ← mul_assoc, ← pow_succ]

section Peirce
variable {p u v : A}

/-- The only needed commutation is derived from opposite-corner support. -/
theorem weight_commutes (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    Commute ⁅u, v⁆ (2 * (u * v + v * u)) := by
  have h := (quadratic_commute_bracket hp hu hv).symm.eq
  change ⁅u, v⁆ * (2 * (u * v + v * u)) =
    (2 * (u * v + v * u)) * ⁅u, v⁆
  calc
    _ = 2 * (⁅u, v⁆ * (u * v + v * u)) := by noncomm_ring
    _ = 2 * ((u * v + v * u) * ⁅u, v⁆) := by rw [h]
    _ = _ := by rw [mul_assoc]

/-- Consume the existing sum step; do not redefine the quadratic frame. -/
theorem weighted_sum_step (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LieAlgebra.ad R A ⁅u, v⁆ (u + v) =
      (2 * (u * v + v * u)) * (u - v) := by
  change ⁅⁅u, v⁆, u + v⁆ = _
  simpa only [two_nsmul, two_mul, add_mul] using bracket_bracket_sum hp hu hv

/-- Consume the existing difference step. -/
theorem weighted_difference_step (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LieAlgebra.ad R A ⁅u, v⁆ (u - v) =
      (2 * (u * v + v * u)) * (u + v) := by
  change ⁅⁅u, v⁆, u - v⁆ = _
  simpa only [two_nsmul, two_mul, add_mul] using bracket_bracket_difference hp hu hv

theorem ad_pow_sum_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (n : ℕ) :
    (LieAlgebra.ad R A ⁅u, v⁆ ^ (2 * n)) (u + v) =
      (2 * (u * v + v * u)) ^ (2 * n) * (u + v) :=
  ad_pow_even_of_reciprocal R (weight_commutes hp hu hv)
    (weighted_sum_step R hp hu hv) (weighted_difference_step R hp hu hv) n

theorem ad_pow_sum_odd (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (n : ℕ) :
    (LieAlgebra.ad R A ⁅u, v⁆ ^ (2 * n + 1)) (u + v) =
      (2 * (u * v + v * u)) ^ (2 * n + 1) * (u - v) :=
  ad_pow_odd_of_reciprocal R (weight_commutes hp hu hv)
    (weighted_sum_step R hp hu hv) (weighted_difference_step R hp hu hv) n

theorem ad_pow_difference_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (n : ℕ) :
    (LieAlgebra.ad R A ⁅u, v⁆ ^ (2 * n)) (u - v) =
      (2 * (u * v + v * u)) ^ (2 * n) * (u - v) :=
  ad_pow_even_of_reciprocal R (weight_commutes hp hu hv)
    (weighted_difference_step R hp hu hv) (weighted_sum_step R hp hu hv) n

theorem ad_pow_difference_odd (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (n : ℕ) :
    (LieAlgebra.ad R A ⁅u, v⁆ ^ (2 * n + 1)) (u - v) =
      (2 * (u * v + v * u)) ^ (2 * n + 1) * (u + v) :=
  ad_pow_odd_of_reciprocal R (weight_commutes hp hu hv)
    (weighted_difference_step R hp hu hv) (weighted_sum_step R hp hu hv) n

/-- A native polynomially generated submodule; no rank is assumed. -/
def frameSpan (u v : A) : Submodule R A :=
  Submodule.span R
    (Set.range (fun n : ℕ => (2 * (u * v + v * u)) ^ n * (u + v)) ∪
     Set.range (fun n : ℕ => (2 * (u * v + v * u)) ^ n * (u - v)))

/-- The full inner action preserves the generated submodule. -/
theorem frameSpan_invariant (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    frameSpan R u v ≤ (frameSpan R u v).comap (LieAlgebra.ad R A ⁅u, v⁆) := by
  refine Submodule.span_le.mpr ?_
  rintro x (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · change LieAlgebra.ad R A ⁅u, v⁆
        ((2 * (u * v + v * u)) ^ n * (u + v)) ∈ frameSpan R u v
    rw [ad_mul_left R ((weight_commutes hp hu hv).pow_right n),
      weighted_sum_step R hp hu hv, ← mul_assoc, ← pow_succ]
    exact Submodule.subset_span (Or.inr ⟨n + 1, rfl⟩)
  · change LieAlgebra.ad R A ⁅u, v⁆
        ((2 * (u * v + v * u)) ^ n * (u - v)) ∈ frameSpan R u v
    rw [ad_mul_left R ((weight_commutes hp hu hv).pow_right n),
      weighted_difference_step R hp hu hv, ← mul_assoc, ← pow_succ]
    exact Submodule.subset_span (Or.inl ⟨n + 1, rfl⟩)

end Peirce
end InfoGeometry.Core.PeirceQuadraticIteration

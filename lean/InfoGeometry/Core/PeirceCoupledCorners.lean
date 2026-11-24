/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceStarCharges

/-!
# Coupling arbitrary opposite Peirce corners

The two inputs are independent elements of the existing directed corner sets.
Their sum is odd, while its square and the bracket of the corners are even.
Reflection interchanges the latter two operators. No commutation, star,
nonvanishing, or cancellation of two is required for the ring identities.
-/

namespace InfoGeometry.Core.PeirceCoupledCorners

open PeirceDecomposition PeirceGrading PeirceStarCharges

variable {A : Type*} [Ring A] {p u v : A}

theorem left_support10 (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    p * u = u := by
  rcases hu with ⟨a, rfl⟩
  exact peirceCorner_absorb_left hp.eq

theorem right_support10 (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    u * p = 0 := by
  rcases hu with ⟨a, rfl⟩
  change (p * a * (1 - p)) * p = 0
  rw [mul_assoc, hp.one_sub_mul_self, mul_zero]

theorem left_support01 (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    p * v = 0 := by
  rcases hv with ⟨b, rfl⟩
  change p * ((1 - p) * b * p) = 0
  calc
    _ = (p * (1 - p)) * b * p := by noncomm_ring
    _ = 0 := by rw [hp.mul_one_sub_self, zero_mul, zero_mul]

theorem right_support01 (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    v * p = v := by
  rcases hv with ⟨b, rfl⟩
  exact peirceCorner_absorb_right hp.eq

theorem component10_fixed (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    component10 p u = u := by
  change p * u * (1 - p) = u
  rw [left_support10 hp hu, mul_sub, mul_one, right_support10 hp hu, sub_zero]

theorem component01_fixed (hp : IsIdempotentElem p) (hv : v ∈ peirce01 p) :
    component01 p v = v := by
  change (1 - p) * v * p = v
  rw [sub_mul, one_mul, left_support01 hp hv, sub_zero, right_support01 hp hv]

theorem component10_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component10 p (u + v) = u := by
  change p * (u + v) * (1 - p) = u
  rw [mul_add, left_support10 hp hu, left_support01 hp hv, add_zero,
    mul_sub, mul_one, right_support10 hp hu, sub_zero]

theorem component01_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component01 p (u + v) = v := by
  change (1 - p) * (u + v) * p = v
  calc
    _ = (1 - p) * (u * p + v * p) := by noncomm_ring
    _ = v := by
      rw [right_support10 hp hu, right_support01 hp hv, zero_add,
        sub_mul, one_mul, left_support01 hp hv, sub_zero]

theorem odd_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    odd p (u + v) = u + v := by
  rw [odd_apply]
  change component10 p (u + v) + component01 p (u + v) = u + v
  rw [component10_coupled hp hu hv, component01_coupled hp hu hv]

theorem coupled_odd (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u + v ∈ LinearMap.range (odd p) := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (odd_idempotent hp)]
  exact odd_coupled hp hu hv

/-- The square expansion is inherited from the existing odd-square owner. -/
theorem coupled_square (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (u + v) ^ 2 = u * v + v * u := by
  calc
    _ = (odd p (u + v)) ^ 2 := by rw [odd_coupled hp hu hv]
    _ = component10 p (u + v) * component01 p (u + v) +
        component01 p (u + v) * component10 p (u + v) := odd_square hp (u + v)
    _ = _ := by rw [component10_coupled hp hu hv, component01_coupled hp hu hv]

theorem left_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    p * (u * v + v * u) = u * v := by
  calc
    _ = p * u * v + p * v * u := by noncomm_ring
    _ = _ := by rw [left_support10 hp hu, left_support01 hp hv, zero_mul, add_zero]

theorem right_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (u * v + v * u) * p = u * v := by
  calc
    _ = u * (v * p) + v * (u * p) := by noncomm_ring
    _ = _ := by rw [right_support01 hp hv, right_support10 hp hu, mul_zero, add_zero]

theorem left_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    p * ⁅u, v⁆ = u * v := by
  change p * (u * v - v * u) = u * v
  calc
    _ = p * u * v - p * v * u := by noncomm_ring
    _ = _ := by rw [left_support10 hp hu, left_support01 hp hv, zero_mul, sub_zero]

theorem right_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ * p = u * v := by
  change (u * v - v * u) * p = u * v
  calc
    _ = u * (v * p) - v * (u * p) := by noncomm_ring
    _ = _ := by rw [right_support01 hp hv, right_support10 hp hu, mul_zero, sub_zero]

theorem component11_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component11 p (u * v + v * u) = u * v := by
  change p * (u * v + v * u) * p = u * v
  rw [left_jordan hp hu hv, mul_assoc, right_support01 hp hv]

theorem component00_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component00 p (u * v + v * u) = v * u := by
  change (1 - p) * (u * v + v * u) * (1 - p) = v * u
  rw [sub_mul, one_mul, left_jordan hp hu hv]
  have h : u * v + v * u - u * v = v * u := by abel
  rw [h, mul_sub, mul_one, mul_assoc, right_support10 hp hu, mul_zero, sub_zero]

theorem component11_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component11 p ⁅u, v⁆ = u * v := by
  change p * ⁅u, v⁆ * p = u * v
  rw [left_bracket hp hu hv, mul_assoc, right_support01 hp hv]

theorem component00_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    component00 p ⁅u, v⁆ = -(v * u) := by
  change (1 - p) * ⁅u, v⁆ * (1 - p) = -(v * u)
  rw [sub_mul, one_mul, left_bracket hp hu hv]
  have h : ⁅u, v⁆ - u * v = -(v * u) := by
    change (u * v - v * u) - u * v = -(v * u)
    abel
  rw [h, neg_mul, mul_sub, mul_one, mul_assoc,
    right_support10 hp hu, mul_zero, sub_zero]

theorem jordan_mem_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * v + v * u ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp, left_jordan hp hu hv, right_jordan hp hu hv]

theorem bracket_mem_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ⁅u, v⁆ ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp, left_bracket hp hu hv, right_bracket hp hu hv]

theorem reflection_mul_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * (u * v + v * u) = ⁅u, v⁆ := by
  change (2 * p - 1) * (u * v + v * u) = u * v - v * u
  simp only [sub_mul, one_mul, two_mul, add_mul, left_jordan hp hu hv]
  abel

theorem reflection_mul_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * ⁅u, v⁆ = u * v + v * u := by
  rw [← reflection_mul_jordan hp hu hv, ← mul_assoc, reflection_sq hp, one_mul]

theorem jordan_eq_zero_iff_bracket_eq_zero (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * v + v * u = 0 ↔ ⁅u, v⁆ = 0 := by
  constructor
  · intro h
    rw [← reflection_mul_jordan hp hu hv, h, mul_zero]
  · intro h
    rw [← reflection_mul_bracket hp hu hv, h, mul_zero]

theorem jordan_eq_zero_iff_products (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u * v + v * u = 0 ↔ u * v = 0 ∧ v * u = 0 := by
  constructor
  · intro h
    constructor
    · have hh := congrArg (component11 p) h
      rw [component11_jordan hp hu hv] at hh
      simpa only [component11, mul_zero, zero_mul] using hh
    · have hh := congrArg (component00 p) h
      rw [component00_jordan hp hu hv] at hh
      simpa only [component00, mul_zero, zero_mul] using hh
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂, zero_add]

theorem coupled_eq_zero_iff (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    u + v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hu0 := congrArg (fun x => p * x) h
    rw [mul_add, left_support10 hp hu, left_support01 hp hv, add_zero, mul_zero] at hu0
    exact ⟨hu0, by simpa only [hu0, zero_add] using h⟩
  · rintro ⟨rfl, rfl⟩
    exact zero_add 0

theorem coupled_conjugation (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * (u + v) * reflection p = -(u + v) := by
  have h := odd_anticommutes_reflection hp (coupled_odd hp hu hv)
  rw [eq_neg_of_add_eq_zero_left h, neg_mul, mul_assoc, reflection_sq hp, mul_one]

theorem jordan_conjugation (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * (u * v + v * u) * reflection p = u * v + v * u := by
  have h := even_commutes_reflection hp (jordan_mem_even hp hu hv)
  rw [h.eq, mul_assoc, reflection_sq hp, mul_one]

theorem bracket_conjugation (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * ⁅u, v⁆ * reflection p = ⁅u, v⁆ := by
  have h := even_commutes_reflection hp (bracket_mem_even hp hu hv)
  rw [h.eq, mul_assoc, reflection_sq hp, mul_one]

section Star

variable [StarRing A]

/-- Taking the star exchanges corners without requiring self-adjoint input. -/
theorem star_component10 (hp : IsSelfAdjoint p) (a : A) :
    star (component10 p a) = component01 p (star a) := by
  simp only [component10, component01, complementIdempotent, star_mul,
    star_sub, star_one, hp.star_eq, mul_assoc]

theorem star_mem_peirce01 (hp : IsSelfAdjoint p) (hu : u ∈ peirce10 p) :
    star u ∈ peirce01 p := by
  rcases hu with ⟨a, rfl⟩
  change star (component10 p a) ∈ peirce01 p
  rw [star_component10 hp]
  exact component01_mem p (star a)

end Star

section MultiplePeirceDecomposition

open scoped BigOperators

variable {ι : Type*}

/-- The `(i, j)` Peirce block `e i * a * e j` associated with an indexed family
of elements `e : ι → A` (McCrimmon, *A Taste of Jordan Algebras*, I.6.3, multiple
Peirce decomposition / matrix archetype rules). -/
def multiPeirceCorner (e : ι → A) (i j : ι) (a : A) : A :=
  e i * a * e j

@[simp]
theorem multiPeirceCorner_apply (e : ι → A) (i j : ι) (a : A) :
    multiPeirceCorner e i j a = e i * a * e j := rfl

/-- **Finite $n$-Block Peirce Decomposition**: if `∑ i, e i = 1`, then every element
`a : A` decomposes as the double sum of its `(i, j)` Peirce corners `e i * a * e j`. -/
theorem multiPeirce_decomposition [Fintype ι] (e : ι → A)
    (hsum : (∑ i : ι, e i) = 1) (a : A) :
    (∑ i : ι, ∑ j : ι, multiPeirceCorner e i j a) = a := by
  have hinner : ∀ i : ι, (∑ j : ι, multiPeirceCorner e i j a) = e i * a := by
    intro i
    calc
      (∑ j : ι, e i * a * e j) = (e i * a) * (∑ j : ι, e j) := by
        rw [Finset.mul_sum]
      _ = e i * a := by rw [hsum, mul_one]
  calc
    (∑ i : ι, ∑ j : ι, multiPeirceCorner e i j a)
        = ∑ i : ι, (e i * a) := Finset.sum_congr rfl (fun i _ => hinner i)
    _ = (∑ i : ι, e i) * a := by rw [Finset.sum_mul]
    _ = a := by rw [hsum, one_mul]

/-- General product of two multi-Peirce corners before applying orthogonality/idempotency. -/
theorem multiPeirceCorner_mul (e : ι → A) (i j k l : ι) (a b : A) :
    multiPeirceCorner e i j a * multiPeirceCorner e k l b =
      e i * a * (e j * e k) * b * e l := by
  simp only [multiPeirceCorner, mul_assoc]

/-- **Matrix Archetype Off-Matching Multiplication Rule** (`P_{ij} · P_{kl} = 0` for `j ≠ k`):
if `e j * e k = 0` whenever `j ≠ k`, the product of mismatched Peirce blocks vanishes. -/
theorem multiPeirceCorner_mul_of_ne (e : ι → A)
    (horth : ∀ ⦃j k : ι⦄, j ≠ k → e j * e k = 0)
    {i j k l : ι} (hjk : j ≠ k) (a b : A) :
    multiPeirceCorner e i j a * multiPeirceCorner e k l b = 0 := by
  rw [multiPeirceCorner_mul, horth hjk, mul_zero, zero_mul, zero_mul]

/-- **Matrix Archetype Matching Multiplication Rule** (`P_{ij} · P_{jk} ⊆ P_{ik}`):
if `e j` is idempotent, the product of matching Peirce blocks `(i, j)` and `(j, k)`
lands inside the `(i, k)` Peirce block. -/
theorem multiPeirceCorner_mul_of_eq (e : ι → A)
    (hidem : ∀ j : ι, IsIdempotentElem (e j))
    (i j k : ι) (a b : A) :
    multiPeirceCorner e i j a * multiPeirceCorner e j k b =
      multiPeirceCorner e i k (a * e j * b) := by
  rw [multiPeirceCorner_mul, (hidem j).eq]
  simp only [multiPeirceCorner, mul_assoc]

/-- **Multi-Peirce Corner Idempotency / Orthogonality**: applying the `(i, j)` corner
projection to a `(k, l)` corner yields the `(i, j)` corner when `(i, j) = (k, l)` and
`0` otherwise. -/
theorem multiPeirceCorner_proj [DecidableEq ι] (e : ι → A)
    (hidem : ∀ i : ι, IsIdempotentElem (e i))
    (horth : ∀ ⦃i j : ι⦄, i ≠ j → e i * e j = 0)
    (i j k l : ι) (a : A) :
    multiPeirceCorner e i j (multiPeirceCorner e k l a) =
      if i = k ∧ j = l then multiPeirceCorner e i j a else 0 := by
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      simp only [and_self, ↓reduceIte, multiPeirceCorner]
      calc
        e i * (e i * a * e j) * e j
            = (e i * e i) * a * (e j * e j) := by simp only [mul_assoc]
        _ = e i * a * e j := by rw [(hidem i).eq, (hidem j).eq]
    · simp only [hjl, and_false, ↓reduceIte, multiPeirceCorner]
      have hlj : l ≠ j := Ne.symm hjl
      calc
        e i * (e i * a * e l) * e j
            = e i * e i * a * (e l * e j) := by simp only [mul_assoc]
        _ = 0 := by rw [horth hlj, mul_zero]
  · simp only [hik, false_and, ↓reduceIte, multiPeirceCorner]
    calc
      e i * (e k * a * e l) * e j
          = (e i * e k) * a * e l * e j := by simp only [mul_assoc]
      _ = 0 := by rw [horth hik, zero_mul, zero_mul, zero_mul]

end MultiplePeirceDecomposition

end InfoGeometry.Core.PeirceCoupledCorners

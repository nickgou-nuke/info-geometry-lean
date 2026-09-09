import Mathlib

/-!
# The `D₅` root multigrading and the split `O(5,5)` contact collapse

The split orthogonal Lie algebra has complex root system

`{ ±eᵢ ± eⱼ | 0 ≤ i < j < 5 }`.

This file records the full `ℤ⁵` root degree and the `|2|`-grading obtained by
collapsing along the first two isotropic directions:

`deg(μ) = μ₀ + μ₁`.

The root-space counts are `(1,12,14,12,1)` and the five Cartan directions add
to degree zero, giving the Lie-grade dimensions `(1,12,19,12,1)` and total
45.  These are finite combinatorial theorems; no physical interpretation is
part of the carrier.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55D5

abbrev Axis := Fin 5

inductive RootSign
  | neg
  | pos
  deriving DecidableEq, Fintype, Repr

namespace RootSign

/-- The coefficient of a signed root coordinate. -/
def value : RootSign → ℤ
  | neg => -1
  | pos => 1

/-- Reversal of a root sign. -/
def flip : RootSign → RootSign
  | neg => pos
  | pos => neg

@[simp] theorem flip_flip (s : RootSign) : s.flip.flip = s := by
  cases s <;> rfl

@[simp] theorem value_flip (s : RootSign) : s.flip.value = -s.value := by
  cases s <;> rfl

@[simp] theorem value_ne_zero (s : RootSign) : s.value ≠ 0 := by
  cases s <;> norm_num [value]

end RootSign

/-- An unordered pair of distinct coordinate axes, represented in increasing
order. -/
abbrev AxisPair := {p : Axis × Axis // p.1 < p.2}

/-- A `D₅` root `sᵢ eᵢ + sⱼ eⱼ`, with `i < j` and `sᵢ,sⱼ ∈ {±1}`. -/
structure Root where
  pair : AxisPair
  leftSign : RootSign
  rightSign : RootSign
  deriving DecidableEq, Fintype, Repr

namespace Root

/-- First active coordinate. -/
def i (r : Root) : Axis := r.pair.1.1

/-- Second active coordinate. -/
def j (r : Root) : Axis := r.pair.1.2

@[simp] theorem i_lt_j (r : Root) : r.i < r.j := r.pair.2

@[simp] theorem i_ne_j (r : Root) : r.i ≠ r.j :=
  ne_of_lt r.i_lt_j

/-- Full `ℤ⁵` multidegree of a `D₅` root. -/
def multiDegree (r : Root) : Axis → ℤ := fun a =>
  (if a = r.i then r.leftSign.value else 0) +
    (if a = r.j then r.rightSign.value else 0)

/-- The `|2|` contact degree associated with the distinguished isotropic
2-plane on axes `0,1`. -/
def contactDegree (r : Root) : ℤ :=
  r.multiDegree 0 + r.multiDegree 1

/-- Root negation preserves the active pair and reverses both signs. -/
def neg (r : Root) : Root where
  pair := r.pair
  leftSign := r.leftSign.flip
  rightSign := r.rightSign.flip

@[simp] theorem neg_neg (r : Root) : r.neg.neg = r := by
  cases r
  simp [neg]

@[simp] theorem multiDegree_neg (r : Root) :
    r.neg.multiDegree = -r.multiDegree := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ls, rs⟩
  have hne : i ≠ j := ne_of_lt hij
  funext a
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    cases ls <;> cases rs <;>
      simp [multiDegree, neg, Root.i, Root.j,
        RootSign.value, RootSign.flip, hai, haj, hne, hne.symm] <;> ring

@[simp] theorem contactDegree_neg (r : Root) :
    r.neg.contactDegree = -r.contactDegree := by
  change r.neg.multiDegree 0 + r.neg.multiDegree 1 =
    -(r.multiDegree 0 + r.multiDegree 1)
  rw [multiDegree_neg r]
  simp only [Pi.neg_apply]
  ring

@[simp] theorem multiDegree_eq_zero_of_ne (r : Root) (a : Axis)
    (hai : a ≠ r.i) (haj : a ≠ r.j) :
    r.multiDegree a = 0 := by
  simp [multiDegree, hai, haj]

/-- Every root has squared Euclidean length two in the integral root lattice. -/
theorem multiDegree_sq_sum (r : Root) :
    ∑ a : Axis, (r.multiDegree a) ^ 2 = 2 := by
  fin_cases r <;> native_decide

/-- The contact collapse takes precisely the five degrees `-2,-1,0,1,2`. -/
theorem contactDegree_cases (r : Root) :
    r.contactDegree = -2 ∨ r.contactDegree = -1 ∨
      r.contactDegree = 0 ∨ r.contactDegree = 1 ∨
        r.contactDegree = 2 := by
  fin_cases r <;> native_decide

end Root

/-- Finite set of roots in one collapsed contact degree. -/
def rootsAt (k : ℤ) : Finset Root :=
  Finset.univ.filter fun r => r.contactDegree = k

/-- Add the rank-five Cartan space to degree zero. -/
def contactGradeDimension (k : ℤ) : ℕ :=
  (rootsAt k).card + if k = 0 then 5 else 0

@[simp] theorem axisPair_card : Fintype.card AxisPair = 10 := by
  native_decide

@[simp] theorem root_card : Fintype.card Root = 40 := by
  native_decide

@[simp] theorem rootsAt_neg_two_card : (rootsAt (-2)).card = 1 := by
  native_decide

@[simp] theorem rootsAt_neg_one_card : (rootsAt (-1)).card = 12 := by
  native_decide

@[simp] theorem rootsAt_zero_card : (rootsAt 0).card = 14 := by
  native_decide

@[simp] theorem rootsAt_one_card : (rootsAt 1).card = 12 := by
  native_decide

@[simp] theorem rootsAt_two_card : (rootsAt 2).card = 1 := by
  native_decide

@[simp] theorem contactGradeDimension_neg_two :
    contactGradeDimension (-2) = 1 := by
  native_decide

@[simp] theorem contactGradeDimension_neg_one :
    contactGradeDimension (-1) = 12 := by
  native_decide

@[simp] theorem contactGradeDimension_zero :
    contactGradeDimension 0 = 19 := by
  native_decide

@[simp] theorem contactGradeDimension_one :
    contactGradeDimension 1 = 12 := by
  native_decide

@[simp] theorem contactGradeDimension_two :
    contactGradeDimension 2 = 1 := by
  native_decide

/-- Dimension check for the split orthogonal algebra `so(5,5)`. -/
theorem contact_five_grade_total_dimension :
    contactGradeDimension (-2) + contactGradeDimension (-1) +
      contactGradeDimension 0 + contactGradeDimension 1 +
        contactGradeDimension 2 = 45 := by
  native_decide

/-- The two extreme grades are exchanged by root negation. -/
theorem neg_bijection_rootsAt (k : ℤ) :
    (rootsAt k).card = (rootsAt (-k)).card := by
  classical
  have hmem : ∀ {r : Root}, r ∈ rootsAt k → r.neg ∈ rootsAt (-k) := by
    intro r hr
    simp only [rootsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [Root.contactDegree_neg]
    simpa using congrArg Neg.neg hr
  have hmem' : ∀ {r : Root}, r ∈ rootsAt (-k) → r.neg ∈ rootsAt k := by
    intro r hr
    simp only [rootsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [Root.contactDegree_neg]
    simpa using congrArg Neg.neg hr
  let e : {r // r ∈ rootsAt k} ≃ {r // r ∈ rootsAt (-k)} :=
    { toFun := fun r => ⟨r.1.neg, hmem r.2⟩
      invFun := fun r => ⟨r.1.neg, hmem' r.2⟩
      left_inv := by intro r; apply Subtype.ext; simp
      right_inv := by intro r; apply Subtype.ext; simp }
  simpa [Fintype.card_coe] using Fintype.card_congr e

/-- The Weyl-coordinate multigrading and its contact collapse, bundled with
the exact dimension packet. -/
theorem d5_multigrading_packet :
    Fintype.card Root = 40 ∧
      (rootsAt (-2)).card = 1 ∧
      (rootsAt (-1)).card = 12 ∧
      (rootsAt 0).card = 14 ∧
      (rootsAt 1).card = 12 ∧
      (rootsAt 2).card = 1 ∧
      contactGradeDimension 0 = 19 ∧
      contactGradeDimension (-2) + contactGradeDimension (-1) +
        contactGradeDimension 0 + contactGradeDimension 1 +
          contactGradeDimension 2 = 45 := by
  exact ⟨root_card, rootsAt_neg_two_card, rootsAt_neg_one_card,
    rootsAt_zero_card, rootsAt_one_card, rootsAt_two_card,
    contactGradeDimension_zero, contact_five_grade_total_dimension⟩

end InfoGeometry.Orthogonal.O55D5

end noncomputable section

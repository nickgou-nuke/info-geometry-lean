/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotencyDefect
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Abel

/-!
# Ordered displacement coordinates for finite matrices

The source index is the column. `weightedShift g d` first applies the source
weight `d`, then translates the index by `g`. Coefficient rings may be
noncommutative. The translation group is abelian; the matrix algebra need not be.

Every matrix has an exact displacement decomposition. Its multiplication law
contains a translated coefficient and preserves the order of the two factors.
This is a coordinate description with all matrix coefficients retained, not a
claim that every matrix has a short sparse factorization.
-/

namespace InfoGeometry.Algebra.MatrixDisplacement

open Matrix
open InfoGeometry.Core.IdempotencyDefect

variable {G R : Type*} [AddCommGroup G] [DecidableEq G] [Ring R]

/-- A column-weighted translation: the rightmost weight acts first. -/
def weightedShift (g : G) (d : G → R) : Matrix G G R :=
  fun i j => if i = g + j then d j else 0

/-- The coefficient of displacement `g` at source `j`. -/
def coefficient (A : Matrix G G R) (g j : G) : R := A (g + j) j

@[simp] theorem weightedShift_apply_source (g : G) (d : G → R) (j : G) :
    weightedShift g d (g + j) j = d j := by
  simp [weightedShift]

@[simp] theorem coefficient_weightedShift (g h : G) (d : G → R) (j : G) :
    coefficient (weightedShift g d) h j = if h = g then d j else 0 := by
  simp [coefficient, weightedShift]

@[simp] theorem weightedShift_zero (d : G → R) :
    weightedShift 0 d = diagonal d := by
  ext i j
  by_cases h : i = j <;> simp [weightedShift, diagonal, h]

theorem weightedShift_add (g : G) (d e : G → R) :
    weightedShift g (fun j => d j + e j) = weightedShift g d + weightedShift g e := by
  ext i j
  simp only [weightedShift, Matrix.add_apply]
  split_ifs <;> simp

theorem weightedShift_sub (g : G) (d e : G → R) :
    weightedShift g (fun j => d j - e j) = weightedShift g d - weightedShift g e := by
  ext i j
  simp only [weightedShift, Matrix.sub_apply]
  split_ifs <;> simp

theorem weightedShift_injective (g : G) :
    Function.Injective (weightedShift (R := R) g) := by
  intro d e h
  funext j
  have hj := congrArg (fun A : Matrix G G R => A (g + j) j) h
  simpa using hj

variable [Fintype G]

/-- Ordered multiplication, with the left coefficient sampled after the right jump. -/
theorem weightedShift_mul (g h : G) (d e : G → R) :
    weightedShift g d * weightedShift h e =
      weightedShift (g + h) (fun j => d (h + j) * e j) := by
  ext i j
  simp [Matrix.mul_apply, weightedShift, mul_ite, ite_mul, add_assoc]

/-- Commuting address translations do not force their weighted matrices to commute. -/
theorem weightedShift_commute_iff (g h : G) (d e : G → R) :
    Commute (weightedShift g d) (weightedShift h e) ↔
      ∀ j, d (h + j) * e j = e (g + j) * d j := by
  change weightedShift g d * weightedShift h e =
    weightedShift h e * weightedShift g d ↔ _
  rw [weightedShift_mul, weightedShift_mul, add_comm h g]
  constructor
  · intro hde j
    exact congrFun (weightedShift_injective (g + h) hde) j
  · intro hde
    exact congrArg (weightedShift (g + h)) (funext hde)

omit [Fintype G] in
/-- Transposition reverses the route and changes which endpoint supplies the weight. -/
theorem weightedShift_transpose (g : G) (hg : g + g = 0) (d : G → R) :
    (weightedShift g d).transpose = weightedShift g (fun j => d (g + j)) := by
  ext i j
  by_cases hij : i = g + j
  · have hji : j = g + i := by rw [hij, ← add_assoc, hg, zero_add]
    change (if j = g + i then d i else 0) = (if i = g + j then d (g + j) else 0)
    rw [ite_eq_left hji, ite_eq_left hij, hij]
  · have hji : j ≠ g + i := by
      intro h
      apply hij
      rw [h, ← add_assoc, hg, zero_add]
    change (if j = g + i then d i else 0) = (if i = g + j then d (g + j) else 0)
    rw [ite_eq_right hji, ite_eq_right hij]

omit [Fintype G] in
theorem weightedShift_symmetric_iff (g : G) (hg : g + g = 0) (d : G → R) :
    (weightedShift g d).transpose = weightedShift g d ↔ ∀ j, d (g + j) = d j := by
  rw [weightedShift_transpose g hg]
  constructor
  · intro h j
    exact congrFun (weightedShift_injective g h) j
  · intro h
    exact congrArg (weightedShift g) (funext h)

omit [Fintype G] in
/-- Two odd coefficient fields produce an even weight and a symmetric operator. -/
theorem weightedShift_odd_product_symmetric (g : G) (hg : g + g = 0)
    (z c : G → R) (hz : ∀ j, z (g + j) = -z j) (hc : ∀ j, c (g + j) = -c j) :
    (weightedShift g (fun j => z j * c j)).transpose =
      weightedShift g (fun j => z j * c j) := by
  apply (weightedShift_symmetric_iff g hg _).2
  intro j
  rw [hz, hc, neg_mul_neg]

/-- An arbitrary matrix has all its coefficients, not just constant shift weights. -/
theorem sum_weightedShift_coefficient (A : Matrix G G R) :
    (∑ g : G, weightedShift g (coefficient A g)) = A := by
  ext i j
  rw [Matrix.sum_apply]
  rw [Finset.sum_eq_single (i - j)]
  · simp [weightedShift, coefficient]
  · intro g _ hg
    have h : i ≠ g + j := by
      intro hij
      apply hg
      simpa using (congrArg (fun x : G => x - j) hij).symm
    simp [weightedShift, h]
  · simp

omit [DecidableEq G] in
/-- Twisted convolution is the exact matrix multiplication law in these coordinates. -/
theorem coefficient_mul (A B : Matrix G G R) (g j : G) :
    coefficient (A * B) g j =
      ∑ h : G, coefficient A (g - h) (h + j) * coefficient B h j := by
  unfold coefficient
  rw [Matrix.mul_apply]
  calc
    (∑ k : G, A (g + j) k * B k j) =
        ∑ h : G, A (g + j) (h + j) * B (h + j) j :=
      (Equiv.sum_comp (Equiv.addRight j) (fun k => A (g + j) k * B k j)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      have he : g - h + (h + j) = g + j := by abel
      rw [he]

theorem coefficient_defect (A : Matrix G G R) (g j : G) :
    coefficient (defect A) g j =
      (∑ h : G, coefficient A (g - h) (h + j) * coefficient A h j) -
        coefficient A g j := by
  change coefficient (A * A) g j - coefficient A g j = _
  rw [coefficient_mul]

/-- Exact recursion in the full operator coefficient system. -/
theorem coefficient_iterate_succ (A : Matrix G G R) (n : ℕ) (g j : G) :
    coefficient (defect^[n + 1] A) g j =
      (∑ h : G, coefficient (defect^[n] A) (g - h) (h + j) *
        coefficient (defect^[n] A) h j) - coefficient (defect^[n] A) g j := by
  rw [Function.iterate_succ_apply', coefficient_defect]

/-- The total displacement of an ordered list of weighted translations. -/
def wordDisplacement (w : List (G × (G → R))) : G := (w.map Prod.fst).sum

/-- The coefficient order follows matrix composition, from the rightmost jump. -/
def wordWeight : List (G × (G → R)) → G → R
  | [], _ => 1
  | (_, d) :: w, j => d (wordDisplacement w + j) * wordWeight w j

/-- A closed formula for a complete ordered path, with no commuting-weight hypothesis. -/
theorem prod_weightedShift (w : List (G × (G → R))) :
    (w.map (fun s => weightedShift s.1 s.2)).prod =
      weightedShift (wordDisplacement w) (wordWeight w) := by
  induction w with
  | nil =>
      ext i j
      simp [wordDisplacement, wordWeight, weightedShift, Matrix.one_apply]
  | cons s w ih =>
      rcases s with ⟨g, d⟩
      simp only [List.map_cons, List.prod_cons, ih, weightedShift_mul]
      rfl

/-- Matrices whose nonzero entries only move within an additive subgroup. -/
def displacementSubring (H : AddSubgroup G) : Subring (Matrix G G R) where
  carrier := {A | ∀ i j, i - j ∉ H → A i j = 0}
  zero_mem' := by simp
  one_mem' := by
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst j
      exact hij (by simp)
    simp [hne]
  add_mem' := by
    intro A B hA hB i j hij
    simp [hA i j hij, hB i j hij]
  neg_mem' := by
    intro A hA i j hij
    simp [hA i j hij]
  mul_mem' := by
    classical
    intro A B hA hB i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i - k ∈ H
    · have hkj : k - j ∉ H := by
        intro h
        apply hij
        simpa using H.add_mem hik h
      rw [hB k j hkj, mul_zero]
    · rw [hA i k hik, zero_mul]

theorem displacementSubring_mono {H K : AddSubgroup G} (h : H ≤ K) :
    displacementSubring (R := R) H ≤ displacementSubring K := by
  intro A hA i j hij
  exact hA i j (fun hc => hij (h hc))

theorem weightedShift_mem (H : AddSubgroup G) (g : G) (d : G → R) (hg : g ∈ H) :
    weightedShift g d ∈ displacementSubring H := by
  intro i j hij
  have hne : i ≠ g + j := by
    intro h
    apply hij
    simpa [h] using hg
  simp [weightedShift, hne]

/-- Defect recursion cannot add a displacement outside the given subgroup. -/
theorem iterate_mem_displacementSubring (H : AddSubgroup G) (A : Matrix G G R)
    (hA : A ∈ displacementSubring H) (n : ℕ) :
    defect^[n] A ∈ displacementSubring H := by
  induction n with
  | zero => simpa using hA
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (displacementSubring H).sub_mem ((displacementSubring H).mul_mem ih ih) ih

/-- One local two-route stage. It has at most two potentially nonzero entries per column. -/
def bitStep (g : G) (d e : G → R) : Matrix G G R :=
  weightedShift 0 d + weightedShift g e

omit [Fintype G] in
theorem bitStep_apply_of_ne (g : G) (d e : G → R) (i j : G)
    (h0 : i ≠ j) (hg : i ≠ g + j) : bitStep g d e i j = 0 := by
  simp [bitStep, weightedShift, h0, hg]

/-- Ordered composition of two stages at the same involutive displacement. -/
theorem bitStep_mul (g : G) (hg : g + g = 0) (d e a b : G → R) :
    bitStep g d e * bitStep g a b =
      bitStep g (fun j => d j * a j + e (g + j) * b j)
        (fun j => d (g + j) * b j + e j * a j) := by
  simp only [bitStep, add_mul, mul_add, weightedShift_mul, zero_add, add_zero, hg]
  rw [weightedShift_add, weightedShift_add]
  abel

/-- The actual local defect update, including its directed mixed coefficient. -/
def bitDefectPair (g : G) (p : (G → R) × (G → R)) : (G → R) × (G → R) :=
  (fun j => p.1 j * p.1 j + p.2 (g + j) * p.2 j - p.1 j,
   fun j => p.1 (g + j) * p.2 j + p.2 j * p.1 j - p.2 j)

theorem defect_bitStep (g : G) (hg : g + g = 0) (d e : G → R) :
    defect (bitStep g d e) =
      bitStep g (bitDefectPair g (d, e)).1 (bitDefectPair g (d, e)).2 := by
  unfold defect
  rw [bitStep_mul g hg]
  simp only [bitStep, bitDefectPair, weightedShift_sub]
  abel

theorem iterate_bitStep (g : G) (hg : g + g = 0) (d e : G → R) (n : ℕ) :
    defect^[n] (bitStep g d e) =
      bitStep g ((bitDefectPair g)^[n] (d, e)).1 ((bitDefectPair g)^[n] (d, e)).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, defect_bitStep g hg,
        Function.iterate_succ_apply']

/-- A fixed bit never creates another scale, even through arbitrary defect depth. -/
theorem iterate_bitStep_apply_of_ne (g : G) (hg : g + g = 0) (d e : G → R)
    (n : ℕ) (i j : G) (h0 : i ≠ j) (h1 : i ≠ g + j) :
    (defect^[n] (bitStep g d e)) i j = 0 := by
  rw [iterate_bitStep g hg]
  exact bitStep_apply_of_ne g _ _ i j h0 h1

/-- Canonical binary addresses; addition is coordinatewise XOR. -/
abbrev BitAddress (n : ℕ) := Fin n → ZMod 2

theorem card_bitAddress (n : ℕ) : Fintype.card (BitAddress n) = 2 ^ n := by
  simp [BitAddress]

theorem bitAddress_add_self (n : ℕ) (g : BitAddress n) : g + g = 0 := by
  ext k
  change g k + g k = 0
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h (g k)

end InfoGeometry.Algebra.MatrixDisplacement

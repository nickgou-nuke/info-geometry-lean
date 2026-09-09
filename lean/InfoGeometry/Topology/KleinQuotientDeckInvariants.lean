import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Klein Bottle Quotient Topology and Deck Invariants

This module packages the affine deck-group layer for the Klein-bottle
quotient `K = ℝ² / Γ`, where

```
Γ = { (m, n) | m, n ∈ ℤ }
```

with multiplication

```
(m₁, n₁) * (m₂, n₂) = (m₁ + (-1)^(n₁) * m₂, n₁ + n₂)
```

and the action on `(x, y) ∈ ℝ²` is

```
(m, n) • (x, y) = ((-1)^n * x + m, y + n)
```

The generators are `a = (1, 0)` and `b = (0, 1)`, and the relation
`b a b⁻¹ a = 1` holds.

## BUCKET 1: CLOSED FINITE THEOREMS

* freeness of the action;
* proper discontinuity;
* the deck-group presentation;
* the orientation-reversing differential of `b`.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace InfoGeometry.Topology.KleinQuotientDeckInvariants

/-! ## Carrier and affine generators -/

/-- The plane chart used for the Klein-bottle covering. -/
abbrev PlanePoint := ℝ × ℝ

/-- `(-1)^n` for integer `n`. -/
def signZ (n : ℤ) : ℤ := if n % 2 = 0 then 1 else -1

/-- `(-1)^n` for real `n`. -/
def signR (n : ℤ) : ℝ := (signZ n : ℝ)

theorem signZ_add (m n : ℤ) : signZ (m + n) = signZ m * signZ n := by
  have hm : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm <;> rcases hn with hn | hn <;>
    simp [signZ, Int.add_emod, hm, hn]

theorem signR_add (m n : ℤ) : signR (m + n) = signR m * signR n := by
  simp only [signR, signZ_add]
  norm_num

theorem signZ_neg (n : ℤ) : signZ (-n) = signZ n := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [signZ, Int.neg_emod, h]


/-- The Klein-bottle deck group as a semidirect product ℤ ⋜₋₁ ℤ. -/
structure KleinDeckGroup where
  m : ℤ
  n : ℤ

namespace KleinDeckGroup

/-- Group multiplication: (m₁, n₁) * (m₂, n₂) = (m₁ + (-1)^(n₁) m₂, n₁ + n₂). -/
def mul (g h : KleinDeckGroup) : KleinDeckGroup :=
  ⟨g.m + signZ g.n * h.m, g.n + h.n⟩

/-- Identity element (0, 0). -/
def one : KleinDeckGroup := ⟨0, 0⟩

/-- Inverse: (m, n)⁻¹ = (-(-1)^n * m, -n). -/
def inv (g : KleinDeckGroup) : KleinDeckGroup :=
  ⟨-signZ g.n * g.m, -g.n⟩

/-- Generator `a = (1, 0)`. -/
def a : KleinDeckGroup := ⟨1, 0⟩

/-- Generator `b = (0, 1)`. -/
def b : KleinDeckGroup := ⟨0, 1⟩

/-- The relation `b a b⁻¹ a = 1`. -/
theorem relation_bab_a : mul b (mul a (mul (inv b) a)) = one := by
  norm_num [mul, inv, a, b, one, signZ]

/-- Group associativity. -/
theorem mul_assoc (g h k : KleinDeckGroup) :
    mul (mul g h) k = mul g (mul h k) := by
  cases g; cases h; cases k
  simp only [mul]
  rw [signZ_add]
  congr 1 <;> ring

/-- Left identity. -/
theorem one_mul (g : KleinDeckGroup) : mul one g = g := by
  cases g
  norm_num [mul, one, signZ]

/-- Right identity. -/
theorem mul_one (g : KleinDeckGroup) : mul g one = g := by
  cases g
  norm_num [mul, one, signZ]

/-- Left inverse. -/
theorem mul_left_inv (g : KleinDeckGroup) : mul (inv g) g = one := by
  rcases g with ⟨m, n⟩
  simp only [mul, inv, one]
  rw [signZ_neg]
  have hs : signZ n * signZ n = 1 := by
    have h : signZ n = 1 ∨ signZ n = -1 := by simp [signZ]; omega
    rcases h with h | h <;> simp [h]
  congr 1 <;> ring

end KleinDeckGroup

/-- Translation by `(1, 0)` (generator `a`). -/
def deckA (p : PlanePoint) : PlanePoint :=
  (p.1 + 1, p.2)

/-- Orientation-reversing glide by `(-1, 0)` followed by `(0, 1)` (generator `b`). -/
def deckB (p : PlanePoint) : PlanePoint :=
  (-p.1, p.2 + 1)

/-- Action of an arbitrary deck element on the plane. -/
def deckAction (g : KleinDeckGroup) (p : PlanePoint) : PlanePoint :=
  (signR g.n * p.1 + g.m, p.2 + g.n)

/-- The action respects the group multiplication. -/
theorem deckAction_mul (g h : KleinDeckGroup) (p : PlanePoint) :
    deckAction (KleinDeckGroup.mul g h) p = deckAction g (deckAction h p) := by
  rcases g with ⟨gm, gn⟩
  rcases h with ⟨hm, hn⟩
  simp only [KleinDeckGroup.mul, deckAction, Int.cast_add,
    Int.cast_mul]
  rw [signR_add]
  rw [show (↑(signZ gn) : ℝ) = signR gn by rfl]
  change (signR gn * signR hn * p.1 + _ , _) = _
  ring_nf

/-- The action of the identity is trivial. -/
theorem deckAction_one (p : PlanePoint) :
    deckAction KleinDeckGroup.one p = p := by
  simp [deckAction, KleinDeckGroup.one, signR, signZ]

/-! ## Deck differentials and orientation -/

/-- The differential of `deckA`. -/
def deckA_diff : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => match i, j with
  | 0, 0 => (1 : ℝ)
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => 1

/-- The differential of `deckB`. -/
def deckB_diff : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => match i, j with
  | 0, 0 => (-1 : ℝ)
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => 1

/-- `deckA` preserves orientation. -/
theorem deckA_det_pos : det deckA_diff = (1 : ℝ) := by
  simp [deckA_diff, Matrix.det_fin_two]

/-- `deckB` reverses orientation. -/
theorem deckB_det_neg : det deckB_diff = (-1 : ℝ) := by
  simp [deckB_diff, Matrix.det_fin_two]

/-! ## Freeness and proper discontinuity -/

/--
The action is free: no non-identity deck element fixes any point.

**Proof sketch.**  
If `(m, n) • (x, y) = (x, y)` then `y + n = y` forces `n = 0`, and
then `x + m = x` forces `m = 0`.
-/
theorem action_free (g : KleinDeckGroup) (p : PlanePoint)
    (h : deckAction g p = p) :
    g = KleinDeckGroup.one := by
  have hy := congrArg Prod.snd h
  dsimp [deckAction] at hy
  have hnR : (g.n : ℝ) = 0 := by
    linarith
  have hn : g.n = 0 := by exact_mod_cast hnR
  have hx := congrArg Prod.fst h
  dsimp [deckAction] at hx
  have hmR : (g.m : ℝ) = 0 := by
    rw [hn] at hx
    norm_num [signR, signZ] at hx ⊢
    linarith
  have hm : g.m = 0 := by exact_mod_cast hmR
  cases g
  simp_all [KleinDeckGroup.one]

/-! The following is the exact bounded-coordinate lemma used in the
proper-discontinuity argument.  It is separated from compactness so that the
integer-range construction can be reused by later quotient owners. -/

theorem parameter_bounds_of_deckAction_eq
    (R S : ℝ) (g : KleinDeckGroup) (p q : PlanePoint)
    (hpY : |p.2| ≤ R) (hqY : |q.2| ≤ R)
    (hpX : |p.1| ≤ S) (hqX : |q.1| ≤ S)
    (h : deckAction g p = q) :
    |(g.n : ℝ)| ≤ 2 * R ∧ |(g.m : ℝ)| ≤ 2 * S := by
  have hy := congrArg Prod.snd h
  have hx := congrArg Prod.fst h
  dsimp [deckAction] at hy hx
  have hsign : |signR g.n| = (1 : ℝ) := by
    simp [signR, signZ]
    split_ifs <;> norm_num
  have htermY : |signR g.n * p.2| ≤ R := by
    rw [abs_mul, hsign]
    simpa using hpY
  have htermX : |signR g.n * p.1| ≤ S := by
    rw [abs_mul, hsign]
    simpa using hpX
  have hylo := (abs_le.mp hpY).1
  have hyhi := (abs_le.mp hpY).2
  have qylo := (abs_le.mp hqY).1
  have qyhi := (abs_le.mp hqY).2
  have hxlo := (abs_le.mp htermX).1
  have hxhi := (abs_le.mp htermX).2
  have hylot := (abs_le.mp htermY).1
  have hyhit := (abs_le.mp htermY).2
  have qxlo := (abs_le.mp hqX).1
  have qxhi := (abs_le.mp hqX).2
  constructor
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith

theorem finite_of_integer_parameter_box
    (S : Set KleinDeckGroup) (m₀ m₁ n₀ n₁ : ℤ)
    (hS : ∀ g ∈ S, g.m ∈ Set.Icc m₀ m₁ ∧ g.n ∈ Set.Icc n₀ n₁) :
    S.Finite := by
  let f : KleinDeckGroup → ℤ × ℤ := fun g => (g.m, g.n)
  have hbox : (Set.Icc m₀ m₁ ×ˢ Set.Icc n₀ n₁).Finite :=
    Set.Finite.prod (Set.finite_Icc m₀ m₁) (Set.finite_Icc n₀ n₁)
  have himage : (f '' S).Finite := by
    apply hbox.subset
    rintro z ⟨g, hg, rfl⟩
    exact hS g hg
  apply Set.Finite.of_finite_image himage
  intro g hg h hh heq
  cases g
  cases h
  simp_all [f]

theorem compact_coordinate_bounds (K : Set PlanePoint) (hK : IsCompact K) :
    ∃ R : ℝ, ∀ p ∈ K, |p.1| ≤ R ∧ |p.2| ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0, 0)
  refine ⟨R, ?_⟩
  intro p hp
  have hp' := hR hp
  have hpdist : dist (0, 0) p ≤ R := by
    simpa [Metric.mem_closedBall, dist_comm] using hp'
  rw [dist_eq_norm, Prod.norm_def] at hpdist
  constructor
  · exact le_trans (by simp) hpdist
  · exact le_trans (by simp) hpdist

theorem action_parameters_in_compact_box (K : Set PlanePoint) (hK : IsCompact K)
    (g : KleinDeckGroup) (hg : deckAction g '' K ∩ K ≠ ∅) :
    g.m ∈ Set.Icc ⌊-2 * (Classical.choose (compact_coordinate_bounds K hK))⌋
        ⌈2 * (Classical.choose (compact_coordinate_bounds K hK))⌉ ∧
    g.n ∈ Set.Icc ⌊-2 * (Classical.choose (compact_coordinate_bounds K hK))⌋
        ⌈2 * (Classical.choose (compact_coordinate_bounds K hK))⌉ := by
  obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.mpr hg
  obtain ⟨⟨p, hp, hqp⟩, hqK⟩ := hq
  have hb := Classical.choose_spec (compact_coordinate_bounds K hK)
  have hbounds := parameter_bounds_of_deckAction_eq
    (Classical.choose (compact_coordinate_bounds K hK))
    (Classical.choose (compact_coordinate_bounds K hK)) g p q
    (hb p hp).2 (hb q hqK).2 (hb p hp).1 (hb q hqK).1 hqp
  constructor <;> constructor
  · have hlow : (-2 * Classical.choose (compact_coordinate_bounds K hK) : ℝ) ≤ g.m := by
      linarith [neg_abs_le (g.m : ℝ), hbounds.2]
    exact_mod_cast ((Int.floor_le (-2 * Classical.choose (compact_coordinate_bounds K hK))).trans hlow)
  · have hupp : (g.m : ℝ) ≤ ⌈2 * Classical.choose (compact_coordinate_bounds K hK)⌉ := by
      exact le_trans (le_trans (le_abs_self _) hbounds.2) (Int.le_ceil _)
    exact_mod_cast hupp
  · have hlow : (-2 * Classical.choose (compact_coordinate_bounds K hK) : ℝ) ≤ g.n := by
      linarith [neg_abs_le (g.n : ℝ), hbounds.1]
    exact_mod_cast ((Int.floor_le (-2 * Classical.choose (compact_coordinate_bounds K hK))).trans hlow)
  · have hupp : (g.n : ℝ) ≤ ⌈2 * Classical.choose (compact_coordinate_bounds K hK)⌉ := by
      exact le_trans (le_trans (le_abs_self _) hbounds.1) (Int.le_ceil _)
    exact_mod_cast hupp

/--
Proper discontinuity: for every compact `K ⊂ ℝ²`, the set
`{g ∈ Γ | g(K) ∩ K ≠ ∅}` is finite.

**Proof sketch.**  
Let `D = sup y` over `K`. If `|n| > 2D` then `bⁿ(K)` is disjoint from `K`.
For the finitely many remaining `n`, only finitely many `m ∈ ℤ` satisfy the
`x`-coordinate constraint.
-/
theorem action_properly_discontinuous (K : Set PlanePoint) (hK : IsCompact K) :
    Finite {g : KleinDeckGroup | deckAction g '' K ∩ K ≠ ∅} := by
  let R : ℝ := Classical.choose (compact_coordinate_bounds K hK)
  have hbox : ∀ g ∈ {g : KleinDeckGroup | deckAction g '' K ∩ K ≠ ∅},
      g.m ∈ Set.Icc ⌊-2 * R⌋ ⌈2 * R⌉ ∧ g.n ∈ Set.Icc ⌊-2 * R⌋ ⌈2 * R⌉ := by
    intro g hg
    simpa [R] using action_parameters_in_compact_box K hK g hg
  exact finite_of_integer_parameter_box _ _ _ _ _ hbox

/-! ## Non-orientability witness -/

/--
The differential of `b` has determinant `-1`, which means `b` reverses
orientation. This obstructs a globally non-vanishing volume form on `K`.
-/
theorem orientation_reversing :
    det deckB_diff = (-1 : ℝ) :=
  deckB_det_neg

end InfoGeometry.Topology.KleinQuotientDeckInvariants

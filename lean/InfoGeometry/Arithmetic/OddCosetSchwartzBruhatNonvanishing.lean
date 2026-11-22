/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Odd Chiral Sector & Coset Schwartz–Bruhat Non-Vanishing

Formalizes Track A Item 2 from the `riemann-masullo` `ERRATA` analysis:

1. **Even / Subgroup-Indicator Vanishing Against Odd Characters**:
   On any finite additive group `G`, any even function `f(-x) = f(x)` — in particular,
   the indicator `1_H` of any origin-centered additive subgroup `H : AddSubgroup G` —
   pairs to `0` against any odd function `χ(-x) = -χ(x)`.
2. **Coset & Antisymmetrized Coset Indicators**:
   Shifted coset indicators `1_{a + H}` and their odd antisymmetrizations
   `1_{a + H} - 1_{-a + H}` survive pairing against odd characters.
3. **Native Mathlib `DirichletCharacter ℂ N` & Explicit `ZMod 3` Witness**:
   Every odd Dirichlet character (`χ (-1) = -1`) satisfies `χ (-x) = -χ x`, vanishes
   against every subgroup indicator `1_H`, and pairs to `1 ≠ 0` against the shifted
   coset indicator `1_{1 + Nℤ}` (and `2 ≠ 0` against the antisymmetrized coset).
-/

noncomputable section

namespace InfoGeometry.Arithmetic.OddCosetSchwartzBruhatNonvanishing

open scoped BigOperators

section FiniteAdditiveGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Indicator function of an origin-centered additive subgroup `H ≤ G`. -/
def subgroupIndicator (H : AddSubgroup G) (x : G) : ℂ := by
  classical
  exact if x ∈ H then 1 else 0

omit [Fintype G] in
/-- Every subgroup indicator is an even function: `1_H(-x) = 1_H(x)`. -/
theorem subgroupIndicator_even (H : AddSubgroup G) (x : G) :
    subgroupIndicator H (-x) = subgroupIndicator H x := by
  classical
  simp [subgroupIndicator, H.neg_mem_iff]

/-- Any even function pairs to `0` against any odd function on a finite additive group. -/
theorem sum_even_mul_odd_eq_zero {f χ : G → ℂ}
    (hf : ∀ x, f (-x) = f x) (hχ : ∀ x, χ (-x) = -χ x) :
    (∑ x : G, f x * χ x) = 0 := by
  have hneg : (∑ x : G, f x * χ x) = -(∑ x : G, f x * χ x) := by
    calc
      (∑ x : G, f x * χ x) = ∑ x : G, f (-x) * χ (-x) :=
        (Fintype.sum_equiv (Equiv.neg G) (fun x => f (-x) * χ (-x))
          (fun x => f x * χ x) (fun _ => rfl)).symm
      _ = ∑ x : G, -(f x * χ x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hf x, hχ x, mul_neg]
      _ = -(∑ x : G, f x * χ x) := Finset.sum_neg_distrib (f := fun x => f x * χ x)
  have h2 : (2 : ℂ) * (∑ x : G, f x * χ x) = 0 := by
    linear_combination hneg
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Every origin-centered subgroup indicator `1_H` annihilates every odd character. -/
theorem sum_subgroupIndicator_mul_odd_eq_zero (H : AddSubgroup G) {χ : G → ℂ}
    (hχ : ∀ x, χ (-x) = -χ x) :
    (∑ x : G, subgroupIndicator H x * χ x) = 0 :=
  sum_even_mul_odd_eq_zero (subgroupIndicator_even H) hχ

/-- Shifted coset indicator `1_{a + H}(x) = 1` iff `x - a ∈ H`. -/
def cosetIndicator (a : G) (H : AddSubgroup G) (x : G) : ℂ := by
  classical
  exact if x - a ∈ H then 1 else 0

/-- Antisymmetrized (odd) coset indicator `1_{a + H} - 1_{-a + H}`. -/
def oddCosetIndicator (a : G) (H : AddSubgroup G) (x : G) : ℂ :=
  cosetIndicator a H x - cosetIndicator (-a) H x

omit [Fintype G] in
/-- `oddCosetIndicator a H` is genuinely odd under `x ↦ -x`. -/
theorem oddCosetIndicator_odd (a : G) (H : AddSubgroup G) (x : G) :
    oddCosetIndicator a H (-x) = -oddCosetIndicator a H x := by
  classical
  have h1 : (-x - a ∈ H) ↔ (x - (-a) ∈ H) := by
    rw [show -x - a = -(x - (-a)) by abel, H.neg_mem_iff]
  have h2 : (-x - (-a) ∈ H) ↔ (x - a ∈ H) := by
    rw [show -x - (-a) = -(x - a) by abel, H.neg_mem_iff]
  simp only [oddCosetIndicator, cosetIndicator, h1, h2]
  ring

/-- Pairing the trivial-subgroup coset indicator `1_{a + 0}` with `χ` evaluates `χ a`. -/
theorem sum_cosetIndicator_bot_mul (a : G) (χ : G → ℂ) :
    (∑ x : G, cosetIndicator a ⊥ x * χ x) = χ a := by
  classical
  have hterm : ∀ x : G, cosetIndicator a ⊥ x * χ x = if x = a then χ a else 0 := by
    intro x
    by_cases hx : x = a
    · subst hx
      simp [cosetIndicator]
    · have hne : x - a ≠ 0 := sub_ne_zero.mpr hx
      simp [cosetIndicator, hne, hx]
  simp [hterm]

/-- Pairing `oddCosetIndicator a ⊥` with any odd `χ` gives `2 * χ a`. -/
theorem sum_oddCosetIndicator_bot_mul (a : G) {χ : G → ℂ} (hχ : ∀ x, χ (-x) = -χ x) :
    (∑ x : G, oddCosetIndicator a ⊥ x * χ x) = 2 * χ a := by
  simp only [oddCosetIndicator, sub_mul, Finset.sum_sub_distrib,
    sum_cosetIndicator_bot_mul, hχ]
  ring

end FiniteAdditiveGroup

/-! ## Native Mathlib `DirichletCharacter ℂ N` Odd-Sector Theorems -/

section DirichletCharacters

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- An odd Dirichlet character (`χ (-1) = -1`) is an odd function on `ZMod N`. -/
theorem dirichletCharacter_odd (χ : DirichletCharacter ℂ N) (hodd : χ (-1) = -1)
    (x : ZMod N) :
    χ (-x) = -χ x := by
  calc
    χ (-x) = χ ((-1 : ZMod N) * x) := by rw [neg_one_mul]
    _ = χ (-1) * χ x := map_mul χ (-1) x
    _ = -χ x := by rw [hodd, neg_one_mul]

/-- Every origin-centered subgroup indicator on `ZMod N` vanishes against any odd
Dirichlet character. -/
theorem sum_subgroupIndicator_mul_odd_dirichlet (H : AddSubgroup (ZMod N))
    (χ : DirichletCharacter ℂ N) (hodd : χ (-1) = -1) :
    (∑ x : ZMod N, subgroupIndicator H x * χ x) = 0 :=
  sum_subgroupIndicator_mul_odd_eq_zero H (dirichletCharacter_odd χ hodd)

/-- The shifted coset indicator `1_{1 + Nℤ}` pairs to `1 ≠ 0` against ANY Dirichlet
character (including odd ones!). -/
theorem sum_cosetOne_dirichletCharacter_eq_one (χ : DirichletCharacter ℂ N) :
    (∑ x : ZMod N, cosetIndicator (1 : ZMod N) ⊥ x * χ x) = 1 := by
  rw [sum_cosetIndicator_bot_mul, map_one]

/-- The antisymmetrized coset indicator `1_{1 + Nℤ} - 1_{-1 + Nℤ}` pairs to `2 ≠ 0`
against every odd Dirichlet character. -/
theorem sum_oddCosetOne_dirichletCharacter_eq_two
    (χ : DirichletCharacter ℂ N) (hodd : χ (-1) = -1) :
    (∑ x : ZMod N, oddCosetIndicator (1 : ZMod N) ⊥ x * χ x) = 2 := by
  rw [sum_oddCosetIndicator_bot_mul (1 : ZMod N) (dirichletCharacter_odd χ hodd),
    map_one, mul_one]

end DirichletCharacters

/-! ## Explicit `ZMod 3` Witness (`1_{1 + 3ℤ}`) -/

/-- Explicit nontrivial odd character modulo `3`: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ -1`. -/
def chiMod3 : ZMod 3 → ℂ
  | 0 => 0
  | 1 => 1
  | 2 => -1

theorem chiMod3_odd (x : ZMod 3) : chiMod3 (-x) = -chiMod3 x := by
  fin_cases x
  · change chiMod3 0 = -chiMod3 0; simp [chiMod3]
  · change chiMod3 2 = -chiMod3 1; simp [chiMod3]
  · change chiMod3 1 = -chiMod3 2; simp [chiMod3]

/-- At `p = 3`, every subgroup indicator kills `chiMod3`, while the shifted coset
`1_{1 + 3ℤ}` pairs to `1 ≠ 0` and `oddCosetIndicator 1 ⊥` pairs to `2 ≠ 0`. -/
theorem zmod3_odd_coset_separation (H : AddSubgroup (ZMod 3)) :
    (∑ x : ZMod 3, subgroupIndicator H x * chiMod3 x) = 0 ∧
      (∑ x : ZMod 3, cosetIndicator (1 : ZMod 3) ⊥ x * chiMod3 x) = 1 ∧
      (∑ x : ZMod 3, oddCosetIndicator (1 : ZMod 3) ⊥ x * chiMod3 x) = 2 := by
  refine ⟨sum_subgroupIndicator_mul_odd_eq_zero H chiMod3_odd, ?_, ?_⟩
  · rw [sum_cosetIndicator_bot_mul]; rfl
  · rw [sum_oddCosetIndicator_bot_mul (1 : ZMod 3) chiMod3_odd]
    change (2 : ℂ) * 1 = 2
    ring

end InfoGeometry.Arithmetic.OddCosetSchwartzBruhatNonvanishing

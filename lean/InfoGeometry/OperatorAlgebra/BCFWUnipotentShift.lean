/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# BCFW shifts as unipotent operators over an operator ring

* For `N² = 0` in any ring: `(1 + N)(1 - N) = 1`, the one-parameter law
  `(1 + m•N)(1 + k•N) = 1 + (m+k)•N` (`m k : ℤ`), `(1 + N)^k = 1 + k•N`, and the conjugation
  formula `(1 + N) X (1 - N) = X + (N X - X N) - N X N`.
* Rank-one operator `N = Z ⊗ W` with operator entries: `W · Z = 0 ⇒ N² = 0`, and
  `N V = Z (W · V)`.
* BCFW column shift: right multiplication by `1 + E_{ji}(z)` (`i ≠ j`, `z` an operator) adds
  `col_j · z` to column `i` and fixes the other columns; it is unipotent with inverse
  `1 + E_{ji}(-z)`.
* `K₄`: the five triangulations of the pentagon and their flip graph, a `5`-cycle.
-/

namespace InfoGeometry.OperatorAlgebra.BCFWUnipotentShift

open Matrix


section Unipotent

variable {A : Type*} [Ring A] {N : A}

theorem unipotent_inverse (hN : N * N = 0) : (1 + N) * (1 - N) = 1 ∧ (1 - N) * (1 + N) = 1 := by
  constructor <;> noncomm_ring <;> simp [hN]

theorem unipotent_flow (hN : N * N = 0) (m k : ℤ) :
    (1 + m • N) * (1 + k • N) = 1 + (m + k) • N := by
  have h : (m • N) * (k • N) = 0 := by rw [smul_mul_smul_comm, hN, smul_zero]
  rw [add_mul, one_mul, mul_add, mul_one, h, add_zero, add_smul]
  abel

theorem unipotent_pow (hN : N * N = 0) (k : ℕ) : (1 + N) ^ k = 1 + (k : ℤ) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have := unipotent_flow hN (k : ℤ) 1
    rw [one_smul] at this
    rw [this]; push_cast; rfl

theorem unipotent_conj (X : A) :
    (1 + N) * X * (1 - N) = X + (N * X - X * N) - N * X * N := by
  noncomm_ring

end Unipotent

section RankOne

variable {A : Type*} [Ring A] {n : Type*} [Fintype n] [DecidableEq n]

/-- `Z ⊗ W` with entries `Z a * W b` in the operator ring. -/
def rankOne (Z W : n → A) : Matrix n n A := Matrix.of fun a b => Z a * W b

/-- `W · Z = Σ W b Z b`. -/
def pair (W Z : n → A) : A := ∑ b, W b * Z b

theorem rankOne_sq (Z W : n → A) (h : pair W Z = 0) : rankOne Z W * rankOne Z W = 0 := by
  ext a c
  simp only [rankOne, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  calc ∑ b, Z a * W b * (Z b * W c) = Z a * (∑ b, W b * Z b) * W c := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        simp only [mul_assoc]
    _ = 0 := by rw [show (∑ b, W b * Z b) = pair W Z from rfl, h, mul_zero, zero_mul]

theorem rankOne_mulVec (Z W V : n → A) (a : n) :
    (rankOne Z W *ᵥ V) a = Z a * pair W V := by
  simp only [rankOne, Matrix.mulVec, dotProduct, Matrix.of_apply, pair, Finset.mul_sum, mul_assoc]

/-- The BCFW flow fixes the shift direction: `W · Z = 0 ⇒ (1 + Z ⊗ W) Z = Z`. -/
theorem rankOne_fix (Z W : n → A) (h : pair W Z = 0) : (1 + rankOne Z W) *ᵥ Z = Z := by
  ext a
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, rankOne_mulVec, h, mul_zero, add_zero]

/-- The BCFW flow shifts any twistor along `Z`: `(1 + Z ⊗ W) V = V + Z (W · V)`. -/
theorem rankOne_shift (Z W V : n → A) (a : n) :
    ((1 + rankOne Z W) *ᵥ V) a = V a + Z a * pair W V := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, rankOne_mulVec]

/-- The flow is unipotent with inverse `1 - Z ⊗ W`. -/
theorem rankOne_flow_inverse (Z W : n → A) (h : pair W Z = 0) :
    (1 + rankOne Z W) * (1 - rankOne Z W) = 1 :=
  (unipotent_inverse (rankOne_sq Z W h)).1

end RankOne

section ColumnShift

variable {A : Type*} [Ring A] {n : Type*} [Fintype n] [DecidableEq n]

/-- Elementary operator with the single entry `z` at `(j, i)`. -/
def elem (j i : n) (z : A) : Matrix n n A := Matrix.of fun a b => if a = j ∧ b = i then z else 0

theorem elem_sq {j i : n} (hji : j ≠ i) (z : A) : elem j i z * elem j i z = 0 := by
  ext a c
  simp only [elem, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  by_cases h1 : a = j ∧ b = i
  · have : ¬ (b = j ∧ c = i) := fun h => hji (h.1 ▸ h1.2)
    simp [this]
  · simp [h1]

/-- BCFW column shift: `C (1 + E_{ji}(z))` adds `col_j · z` to column `i`, other columns fixed. -/
theorem column_shift {m : Type*} (C : Matrix m n A) {j i : n} (z : A) (r : m) (c : n) :
    (C * (1 + elem j i z : Matrix n n A)) r c = C r c + if c = i then C r j * z else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  simp only [elem, Matrix.mul_apply, Matrix.of_apply]
  by_cases hc : c = i
  · subst hc; simp
  · simp [hc]

theorem column_shift_inverse {j i : n} (hji : j ≠ i) (z : A) :
    (1 + elem j i z) * (1 + elem j i (-z)) = 1 := by
  have hneg : elem j i (-z) = -elem j i z := by
    ext a b; simp only [elem, Matrix.of_apply, Matrix.neg_apply]; split_ifs <;> simp
  rw [hneg]
  exact (unipotent_inverse (elem_sq hji z)).1 |> fun h => by simpa [sub_eq_add_neg] using h

end ColumnShift

/-! ### `K₄`: triangulations of the pentagon and the flip `5`-cycle -/

section Pentagon

/-- Triangulation `k` of the pentagon `0…4`: the two diagonals from vertex `k`. -/
def triang (k : Fin 5) : Finset (Fin 5 × Fin 5) := {(k, k + 2), (k, k + 3)}

/-- Two triangulations are related by a flip iff they share exactly one diagonal
(as unordered pairs). -/
def sym (d : Fin 5 × Fin 5) : Finset (Fin 5) := {d.1, d.2}

def diagSet (k : Fin 5) : Finset (Finset (Fin 5)) := (triang k).image sym

def flip (k l : Fin 5) : Prop := (diagSet k ∩ diagSet l).card = 1

instance (k l : Fin 5) : Decidable (flip k l) := by unfold flip; infer_instance

theorem diagSet_card (k : Fin 5) : (diagSet k).card = 2 := by revert k; decide

theorem diagSet_injective : Function.Injective diagSet := by decide

/-- The flip graph of the five triangulations is the `5`-cycle `k ~ k ± 2`. -/
theorem flip_iff (k l : Fin 5) : flip k l ↔ (l = k + 2 ∨ l = k + 3) := by revert k l; decide

end Pentagon

end InfoGeometry.OperatorAlgebra.BCFWUnipotentShift

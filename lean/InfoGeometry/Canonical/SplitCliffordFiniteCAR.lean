import Mathlib
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR

/-!
# InfoGeometry.Canonical.SplitCliffordFiniteCAR

Indexed finite CAR core over the concrete two-mode Jordan-Wigner model.
No wrappers. No placeholders.
-/

namespace InfoGeometry.Canonical.SplitCliffordFiniteCAR

open Matrix
open Filter
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ
abbrev Mode := Fin 2

/-- Associative commutator on `M4R`. -/
def commM4 (X Y : M4R) : M4R :=
  X * Y - Y * X

/-- Indexed annihilation operators on two modes. -/
def aMode : Mode → M4R
  | 0 => a1
  | 1 => a2

/-- Indexed creation operators on two modes. -/
def adagMode : Mode → M4R
  | 0 => a1Dag
  | 1 => a2Dag

/-- Same-mode CAR (indexed). -/
theorem same_mode_car (i : Mode) :
    aMode i * adagMode i + adagMode i * aMode i = (1 : M4R) := by
  fin_cases i
  · simpa [aMode, adagMode] using mode1_car_identity
  · simpa [aMode, adagMode] using mode2_car_identity

/-- Distinct annihilation modes anticommute (indexed). -/
theorem cross_annihilate_anticomm
    (i j : Mode) (hij : i ≠ j) :
    aMode i * aMode j + aMode j * aMode i = (0 : M4R) := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · simpa [aMode] using cross_annihilate_anticommute
  · simpa [aMode, add_comm] using cross_annihilate_anticommute

/-- Distinct mixed CAR vanishing (indexed). -/
theorem cross_mixed_anticomm
    (i j : Mode) (hij : i ≠ j) :
    aMode i * adagMode j + adagMode j * aMode i = (0 : M4R) := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · simpa [aMode, adagMode] using cross_mixed_anticommute
  ·
    ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [aMode, adagMode, a1Dag, a2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Finite indexed current family with support on modes `±1`. -/
def JfinIndexed (n : Int) : M4R :=
  if n = 1 then adagMode 0 * aMode 1 else if n = -1 then adagMode 1 * aMode 0 else 0

/-- Support vanishing for indexed finite current family. -/
theorem JfinIndexed_eq_zero_of_ne_one_ne_neg_one
    (n : Int) (hne1 : n ≠ 1) (hneNeg1 : n ≠ -1) :
    JfinIndexed n = 0 := by
  simp [JfinIndexed, hne1, hneNeg1]

/-- Exact support table for the indexed finite current family. -/
theorem JfinIndexed_eq_zero_iff (n : Int) :
    JfinIndexed n = 0 ↔ n ≠ 1 ∧ n ≠ -1 := by
  constructor
  · intro h
    constructor
    · intro hn
      rw [hn] at h
      have hentry := congrArg (fun M : M4R => M 2 1) h
      norm_num [JfinIndexed, aMode, adagMode, Matrix.mul_apply, Fin.sum_univ_four] at hentry
      have h01 : (1 : ℝ) = 0 := by
        simpa [a1Dag, a2] using hentry
      norm_num at h01
    · intro hn
      rw [hn] at h
      have hentry := congrArg (fun M : M4R => M 1 2) h
      norm_num [JfinIndexed, aMode, adagMode, Matrix.mul_apply, Fin.sum_univ_four] at hentry
      have h01 : (1 : ℝ) = 0 := by
        simpa [a2Dag, a1] using hentry
      norm_num at h01
  · rintro ⟨h1, hm1⟩
    exact JfinIndexed_eq_zero_of_ne_one_ne_neg_one n h1 hm1

/-- Mode-indexed finite current seed `Jᵢⱼ = aᵢ† aⱼ`. -/
def Jmode (i j : Mode) : M4R :=
  adagMode i * aMode j

/-- Two-mode support modes for `JfinIndexed`. -/
theorem JfinIndexed_eval_one :
    JfinIndexed 1 = Jmode 0 1 := by
  simp [JfinIndexed, Jmode, aMode, adagMode]

/-- Two-mode support modes for `JfinIndexed`. -/
theorem JfinIndexed_eval_neg_one :
    JfinIndexed (-1) = Jmode 1 0 := by
  simp [JfinIndexed, Jmode, aMode, adagMode]

/-- Mode-indexed commutator table: `[J01, J01] = 0`. -/
theorem Jmode_comm_01_01 :
    commM4 (Jmode 0 1) (Jmode 0 1) = 0 := by
  simp [commM4, Jmode]

/-- Mode-indexed commutator table: `[J10, J10] = 0`. -/
theorem Jmode_comm_10_10 :
    commM4 (Jmode 1 0) (Jmode 1 0) = 0 := by
  simp [commM4, Jmode]

/-- Mode-indexed commutator table: explicit nontrivial `[J01, J10]`. -/
theorem Jmode_comm_01_10 :
    commM4 (Jmode 0 1) (Jmode 1 0) =
      !![0, 0, 0, 0;
         0, -1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [commM4, Jmode, aMode, adagMode, a1, a1Dag, a2, a2Dag,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Mode-indexed commutator table: reverse orientation. -/
theorem Jmode_comm_10_01 :
    commM4 (Jmode 1 0) (Jmode 0 1) =
      - !![0, 0, 0, 0;
           0, -1, 0, 0;
           0, 0, 1, 0;
           0, 0, 0, 0] := by
  calc
    commM4 (Jmode 1 0) (Jmode 0 1)
        = -commM4 (Jmode 0 1) (Jmode 1 0) := by
          unfold commM4
          abel
    _ = - !![0, 0, 0, 0;
             0, -1, 0, 0;
             0, 0, 1, 0;
             0, 0, 0, 0] := by
          rw [Jmode_comm_01_10]

/-- Indexed support-commutator vanishing outside `±1`. -/
theorem JfinIndexed_comm_zero_of_outside_support
    {m n : Int}
    (h : (m ≠ 1 ∧ m ≠ -1) ∨ (n ≠ 1 ∧ n ≠ -1)) :
    commM4 (JfinIndexed m) (JfinIndexed n) = 0 := by
  rcases h with hm | hn
  · rw [JfinIndexed_eq_zero_of_ne_one_ne_neg_one m hm.1 hm.2]
    simp [commM4]
  · rw [JfinIndexed_eq_zero_of_ne_one_ne_neg_one n hn.1 hn.2]
    simp [commM4]

/-- Indexed truncation at `+∞`, vector form. -/
theorem JfinIndexed_trunc_vector (v : Fin 4 → ℝ) :
    ∀ᶠ l : Int in atTop, JfinIndexed l *ᵥ v = 0 := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, ?_⟩
  intro l hl
  have hne1 : l ≠ 1 := by linarith
  have hneNeg1 : l ≠ -1 := by linarith
  rw [JfinIndexed_eq_zero_of_ne_one_ne_neg_one l hne1 hneNeg1]
  simp

end InfoGeometry.Canonical.SplitCliffordFiniteCAR

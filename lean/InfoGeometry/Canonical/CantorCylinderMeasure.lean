import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.CantorColimitProjectiveBoundaryBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace InfoGeometry.Canonical.CantorCylinderMeasure

open InfoGeometry.Canonical.CantorColimitProjectiveBoundaryBridge
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- 1. Bernoulli Probability Weight for a BitWord w of length n with parameter p ∈ (0, 1) -/
def bernoulliWeight {n : ℕ} (p : ℝ) (w : BitWord n) : ℝ :=
  ∏ i : Fin n, (if w i = 0 then p else (1 - p))

/-- 🏆 THEOREM 1: Positivity of Bernoulli Cylinder Measure for p ∈ (0, 1) -/
theorem bernoulliWeight_pos {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (w : BitWord n) :
    0 < bernoulliWeight p w := by
  dsimp [bernoulliWeight]
  refine Finset.prod_pos (fun i _ => ?_)
  split_ifs
  · exact hp0
  · linarith

/-- 🏆 THEOREM 2: Binary Child Cylinder Measure Additivity:
    μ([w 0]) + μ([w 1]) = μ([w]) -/
theorem bernoulliWeight_child_sum {n : ℕ} (p : ℝ) (w : BitWord n) :
    let w0 : BitWord (n + 1) := fun i => if h : i.1 < n then w ⟨i.1, h⟩ else 0
    let w1 : BitWord (n + 1) := fun i => if h : i.1 < n then w ⟨i.1, h⟩ else 1
    bernoulliWeight p w0 + bernoulliWeight p w1 = bernoulliWeight p w := by
  intro w0 w1
  dsimp [bernoulliWeight]
  rw [Fin.prod_univ_castSucc]
  rw [Fin.prod_univ_castSucc]
  have h_w0_last : (if w0 (Fin.last n) = 0 then p else 1 - p) = p := by
    dsimp [w0, Fin.last]
    have hlt : ¬ n < n := Nat.lt_irrefl n
    rw [dif_neg hlt]
    simp
  have h_w1_last : (if w1 (Fin.last n) = 0 then p else 1 - p) = 1 - p := by
    dsimp [w1, Fin.last]
    have hlt : ¬ n < n := Nat.lt_irrefl n
    rw [dif_neg hlt]
    simp
  have h_w0_prefix : (fun i : Fin n => if w0 i.castSucc = 0 then p else 1 - p) =
                     (fun i : Fin n => if w i = 0 then p else 1 - p) := by
    ext i
    dsimp [w0, Fin.castSucc]
    have hlt : i.1 < n := i.is_lt
    simp [hlt]
  have h_w1_prefix : (fun i : Fin n => if w1 i.castSucc = 0 then p else 1 - p) =
                     (fun i : Fin n => if w i = 0 then p else 1 - p) := by
    ext i
    dsimp [w1, Fin.castSucc]
    have hlt : i.1 < n := i.is_lt
    simp [hlt]
  rw [h_w0_prefix, h_w1_prefix, h_w0_last, h_w1_last]
  rw [← mul_add]
  ring

/-- 🏆 THEOREM 3: Total Cylinder Measure Sum Normalized to 1 for n = 1 -/
theorem bernoulliWeight_sum_one_n1 (p : ℝ) :
    let w0 : BitWord 1 := fun _ => 0
    let w1 : BitWord 1 := fun _ => 1
    bernoulliWeight p w0 + bernoulliWeight p w1 = 1 := by
  intro w0 w1
  dsimp [bernoulliWeight, w0, w1]
  simp

end InfoGeometry.Canonical.CantorCylinderMeasure

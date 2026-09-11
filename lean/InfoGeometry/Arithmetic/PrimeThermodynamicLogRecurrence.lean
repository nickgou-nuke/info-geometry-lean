import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeThermodynamicLogRecurrence

def stageProduct {α : Type*} (S : Finset α) (w : α → ℝ) : ℝ :=
  ∏ x ∈ S, w x

def stageLogIncrement (q : ℝ) : ℝ :=
  Real.log q

theorem stageProduct_insert
    {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α) (w : α → ℝ) (ha : a ∉ S) :
    stageProduct (insert a S) w = w a * stageProduct S w := by
  unfold stageProduct
  rw [Finset.prod_insert ha]

theorem stageProduct_pos
    {α : Type*} (S : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ S, 0 < w a) :
    0 < stageProduct S w := by
  unfold stageProduct
  exact Finset.prod_pos hw

theorem stageProduct_ne_zero
    {α : Type*} (S : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ S, 0 < w a) :
    stageProduct S w ≠ 0 :=
  (stageProduct_pos S w hw).ne'

theorem stageProduct_union
    {α : Type*} [DecidableEq α] (S T : Finset α) (w : α → ℝ)
    (hST : Disjoint S T) :
    stageProduct (S ∪ T) w = stageProduct S w * stageProduct T w := by
  unfold stageProduct
  rw [Finset.prod_union hST]

theorem stageLogProduct_union
    {α : Type*} [DecidableEq α] (S T : Finset α) (w : α → ℝ)
    (hST : Disjoint S T)
    (hS : ∀ a ∈ S, 0 < w a)
    (hT : ∀ a ∈ T, 0 < w a) :
    Real.log (stageProduct (S ∪ T) w) =
      Real.log (stageProduct S w) + Real.log (stageProduct T w) := by
  rw [stageProduct_union S T w hST]
  simpa using Real.log_mul (stageProduct_ne_zero S w hS)
    (stageProduct_ne_zero T w hT)

theorem stageLogIncrement_eq_log
    (q : ℝ) : stageLogIncrement q = Real.log q := rfl

theorem stageLogProduct_insert
    {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α) (w : α → ℝ) (ha : a ∉ S)
    (hqa : w a ≠ 0)
    (hS : stageProduct S w ≠ 0) :
    Real.log (stageProduct (insert a S) w) =
      Real.log (stageProduct S w) + stageLogIncrement (w a) := by
  rw [stageProduct_insert S a w ha, stageLogIncrement_eq_log]
  simpa [add_comm] using Real.log_mul hqa hS

theorem stageLogProduct_insert_pos
    {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α) (w : α → ℝ) (ha : a ∉ S)
    (hw : ∀ x ∈ insert a S, 0 < w x) :
    Real.log (stageProduct (insert a S) w) =
      Real.log (stageProduct S w) + stageLogIncrement (w a) := by
  apply stageLogProduct_insert S a w ha
  · exact (hw a (by simp)).ne'
  · exact stageProduct_ne_zero S w (fun x hx => hw x (by simp [hx]))

end InfoGeometry.Arithmetic.PrimeThermodynamicLogRecurrence

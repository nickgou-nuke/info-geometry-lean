import InfoGeometry.RegularizedKL
import Mathlib.Tactic

namespace RegularizedKLTest

open StatisticalMechanics

-- basic sanity checks for the new regularization module

example {α : Type} [Fintype α] [Nonempty α]
    (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
  0 < regTotalCount count ε :=
  regTotalCount_pos count ε hε

example {α : Type} [Fintype α] [Nonempty α]
    (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
  0 < regularizedPMF count ε hε x :=
  regularizedPMF_strictly_pos count ε hε x

example {α : Type} [Fintype α] [Nonempty α]
    (countP countQ : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
  0 < (regularizedPMF countP ε hε x) / (regularizedPMF countQ ε hε x) :=
  regularized_kl_is_safe countP countQ ε hε x

example {α : Type} [Fintype α] [Nonempty α]
    (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∑ x : α, regularizedPMF count ε hε x = 1 :=
  sum_regularizedPMF_eq_one count ε hε

example {α : Type} [Fintype α] [Nonempty α]
    (count : α → ℕ) (ε : ℝ) (hε : 0 < ε) (x : α) :
    0 ≤ regularizedPMF count ε hε x :=
  le_of_lt (regularizedPMF_strictly_pos count ε hε x)

-- concrete Bool example just to exercise the definitions
example :
  0 <
    (regularizedPMF (fun b : Bool => if b then 3 else 1) (0.1 : ℝ) (by norm_num) true) /
      (regularizedPMF (fun b : Bool => if b then 2 else 2) (0.1 : ℝ) (by norm_num) true) := by
  have hε : 0 < (0.1 : ℝ) := by norm_num
  simpa using
    (regularized_kl_is_safe
      (countP := fun b : Bool => if b then 3 else 1)
      (countQ := fun b : Bool => if b then 2 else 2)
      (ε := (0.1 : ℝ))
      hε
      (x := true))

end RegularizedKLTest

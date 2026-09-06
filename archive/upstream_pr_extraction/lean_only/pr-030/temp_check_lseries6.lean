import Mathlib
import Mathlib.NumberTheory.LSeries.Dirichlet

open Complex

noncomputable section

def dirichletSeriesZeta (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((n : ℂ) ^ (-s))

theorem test_dirichlet_eq (s : ℂ) (hs : 1 < s.re) :
    dirichletSeriesZeta s = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  unfold LSeries dirichletSeriesZeta LSeries.term
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · simp [h]
    rw [cpow_neg]
    rfl

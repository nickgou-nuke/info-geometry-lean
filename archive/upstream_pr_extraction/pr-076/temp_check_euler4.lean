import Mathlib
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open Complex

noncomputable section

def eulerProductZeta (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹

theorem test_euler_eq (s : ℂ) (hs : 1 < s.re) :
    eulerProductZeta s = riemannZeta s := by
  unfold eulerProductZeta
  exact riemannZeta_eulerProduct_tprod hs

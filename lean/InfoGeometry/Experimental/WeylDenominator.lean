import Mathlib.Algebra.BigOperators.Ring.Finset
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open scoped BigOperators
open Complex

namespace InfoGeometry.Experimental.WeylDenominator

/-- A finite Weyl denominator indexed by prime generators. -/
noncomputable def finiteWeylDenominator (S : Finset Nat.Primes) (s : ℂ) : ℂ :=
  S.prod fun p => (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹

/-- The prime gas partition function readout. -/
noncomputable def primeGasPartitionFunction (s : ℂ) : ℂ :=
  riemannZeta s

/-- Zeta bridge from the Euler product. -/
theorem weyl_denominator_limit_eq_inv_zeta
    (h_conv : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) = riemannZeta s := by
  simpa using riemannZeta_eulerProduct_tprod h_conv

end InfoGeometry.Experimental.WeylDenominator

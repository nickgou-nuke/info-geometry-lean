import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Experimental.WeylDenominator

open scoped BigOperators
open Complex

namespace InfoGeometry.Canonical

/-- The exact prime gas partition structure matching the physics readout. -/
structure PrimeGasPartition where
  convergenceDomain : ℂ → Prop
  partitionFunction : ℂ → ℂ
  eulerProduct      : ℂ → ℂ

/-- 
  The specialization gate. Notice we use the exact `↑↑p` double coercion:
  Nat.Primes → ℕ → ℂ, which prevents subtype elaboration failures.
-/
structure PrimeWeightSpecialization (P : PrimeGasPartition) where
  partition_eq_eulerProduct :
    ∀ s, P.partitionFunction s = P.eulerProduct s
  eulerProduct_eq_prime_tprod :
    ∀ s, P.eulerProduct s = ∏' (p : Nat.Primes), (1 - ↑↑p ^ (-s))⁻¹

/-- The exact arithmetic bridge wrapping Mathlib's Dirichlet owner theorem. -/
theorem zeta_trace_bridge {s : ℂ} (hs : 1 < s.re) :
    (∏' (p : Nat.Primes), (1 - ↑↑p ^ (-s))⁻¹) = riemannZeta s := by
  simpa using riemannZeta_eulerProduct_tprod hs

/-- Compatibility alias for the Weyl denominator bridge. -/
theorem weyl_denominator_limit_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    ∏' (p : Nat.Primes), (1 - ↑↑p ^ (-s))⁻¹ = riemannZeta s :=
  zeta_trace_bridge hs

/-- The final Klein-Hestenes invariant readout. -/
theorem PrimeWeightSpecialization.partitionFunction_eq_riemannZeta
    {P : PrimeGasPartition}
    (W : PrimeWeightSpecialization P)
    {s : ℂ}
    (hs : 1 < s.re) :
    P.partitionFunction s = riemannZeta s := by
  rw [W.partition_eq_eulerProduct s, W.eulerProduct_eq_prime_tprod s, zeta_trace_bridge hs]

end InfoGeometry.Canonical

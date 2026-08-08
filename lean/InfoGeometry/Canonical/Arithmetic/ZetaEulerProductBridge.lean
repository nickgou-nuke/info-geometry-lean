import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing

open scoped BigOperators
open Complex

noncomputable section

namespace InfoGeometry.Canonical.Arithmetic

/-! ### 1. The Multiplicative Symmetry Carrier -/

/--
The abstract prime-gas partition carrier.
Instead of raw analytic functions, we define a structured state containing:
- A convergence domain check.
- An abstract partition function.
- An Euler-product representation.
-/
abbrev PrimeGasPartition :=
  (ℂ → Prop) × (ℂ → ℂ) × (ℂ → ℂ)

/-- Compatibility accessor for the convergence domain. -/
abbrev PrimeGasPartition.convergenceDomain (P : PrimeGasPartition) : ℂ → Prop := P.1

/-- Compatibility accessor for the abstract partition function. -/
abbrev PrimeGasPartition.partitionFunction (P : PrimeGasPartition) : ℂ → ℂ := P.2.1

/-- Compatibility accessor for the Euler-product readout. -/
abbrev PrimeGasPartition.eulerProduct (P : PrimeGasPartition) : ℂ → ℂ := P.2.2

namespace PrimeGasPartition

/-- The finite volume/partial partition function. -/
def finiteEulerProduct (S : Finset Nat.Primes) (s : ℂ) : ℂ :=
  S.prod fun p => (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹

@[simp]
theorem finiteEulerProduct_empty (s : ℂ) :
    finiteEulerProduct (∅ : Finset Nat.Primes) s = 1 := by
  simp [finiteEulerProduct]

theorem finiteEulerProduct_insert {S : Finset Nat.Primes} {p : Nat.Primes}
    (hp : p ∉ S) (s : ℂ) :
    finiteEulerProduct (insert p S) s =
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ * finiteEulerProduct S s := by
  rw [finiteEulerProduct, Finset.prod_insert hp, finiteEulerProduct]

@[simp]
theorem finiteEulerProduct_singleton (p : Nat.Primes) (s : ℂ) :
    finiteEulerProduct ({p} : Finset Nat.Primes) s =
      (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ := by
  simp [finiteEulerProduct]

end PrimeGasPartition

/-! ### 2. Analytic Gates and Specialization -/

/-- The Analytic Gate ensuring physical convergence of the partition function. -/
abbrev AnalyticGate (P : PrimeGasPartition) :=
  {β : ℂ // 1 < β.re ∧ P.convergenceDomain β}

namespace AnalyticGate

/-- Compatibility accessor for the gated complex parameter. -/
abbrev β (G : AnalyticGate P) : ℂ := G.1

/-- Compatibility accessor for the half-plane property. -/
abbrev re_gt_one (G : AnalyticGate P) : 1 < G.β.re := G.2.1

/-- Compatibility accessor for membership in the declared domain. -/
abbrev inDomain (G : AnalyticGate P) : P.convergenceDomain G.β := G.2.2

end AnalyticGate

/-- The exact prime-weight specialization bridging abstract states to `Nat.Primes`. -/
abbrev PrimeWeightSpecialization (P : PrimeGasPartition) :=
  (∀ s, P.partitionFunction s = P.eulerProduct s) ∧
    (∀ s, P.eulerProduct s = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹)

namespace PrimeWeightSpecialization

/-- Compatibility accessor for the partition/Euler-product equality. -/
abbrev partition_eq_eulerProduct (W : PrimeWeightSpecialization P) :
    ∀ s, P.partitionFunction s = P.eulerProduct s := W.1

/-- Compatibility accessor for the prime Euler-product equality. -/
abbrev eulerProduct_eq_prime_tprod (W : PrimeWeightSpecialization P) :
    ∀ s, P.eulerProduct s = ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ := W.2

end PrimeWeightSpecialization

/-! ### 3. The Final Invariant Readout (The Bridge) -/

/--
Zeta-Euler Product Bridge (Direct wrapper):
The prime multiplicative carrier has Euler-product invariant `riemannZeta`
in the convergence region `1 < s.re`.
-/
theorem zeta_euler_product_bridge {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) = riemannZeta s := by
  simpa using riemannZeta_eulerProduct_tprod hs

/--
The structured theorem: The `PrimeGasPartition` canonically evaluates to
the Riemann zeta function when specialized to prime weights and passed
through the `Re(s) > 1` analytic gate.
-/
theorem PrimeWeightSpecialization.partitionFunction_eq_riemannZeta
    {P : PrimeGasPartition}
    (W : PrimeWeightSpecialization P)
    {s : ℂ}
    (hs : 1 < s.re) :
    P.partitionFunction s = riemannZeta s := by
  calc
    P.partitionFunction s = P.eulerProduct s :=
      W.partition_eq_eulerProduct s
    _ = (∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) :=
      W.eulerProduct_eq_prime_tprod s
    _ = riemannZeta s :=
      zeta_euler_product_bridge hs

end InfoGeometry.Canonical.Arithmetic

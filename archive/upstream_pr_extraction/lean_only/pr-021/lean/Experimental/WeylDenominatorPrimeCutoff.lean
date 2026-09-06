import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing

noncomputable section

open scoped BigOperators

namespace Experimental.WeylDenominatorPrimeCutoff

/--
Prime-gas carrier.

Klein/Hestenes reading:
the prime index type is the multiplicative symmetry carrier;
`energyOfPrime` is the additive logarithmic coordinate;
`partitionFunction` and `eulerProduct` are scalar readouts.
-/
structure PrimeGasPartition where
  primeIndex : Type
  prime : primeIndex → Nat.Primes
  prime_isPrime : ∀ i, Nat.Prime (prime i : ℕ)
  energyOfPrime : primeIndex → ℝ
  convergenceDomain : ℂ → Prop
  partitionFunction : ℂ → ℂ
  eulerProduct : ℂ → ℂ

namespace PrimeGasPartition

/-- The carrier energy coordinate. -/
def primeEnergy (P : PrimeGasPartition) (i : P.primeIndex) : ℝ :=
  P.energyOfPrime i

@[simp]
lemma primeEnergy_eq_energyOfPrime
    (P : PrimeGasPartition) (i : P.primeIndex) :
    P.primeEnergy i = P.energyOfPrime i := rfl

/-- Finite multiplicative template for the Euler/Weyl-style product. -/
def finiteEulerProduct (s : ℂ) (S : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ S, (1 - (p : ℂ) ^ (-s))⁻¹

@[simp]
lemma finiteEulerProduct_empty (s : ℂ) :
    finiteEulerProduct s ∅ = 1 := by
  unfold finiteEulerProduct
  simp

lemma finiteEulerProduct_insert
    (s : ℂ) {S : Finset Nat.Primes} {p : Nat.Primes}
    (hp : p ∉ S) :
    finiteEulerProduct s (insert p S) =
      (1 - (p : ℂ) ^ (-s))⁻¹ * finiteEulerProduct s S := by
  unfold finiteEulerProduct
  rw [Finset.prod_insert hp]

@[simp]
lemma finiteEulerProduct_singleton (s : ℂ) (p : Nat.Primes) :
    finiteEulerProduct s {p} = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  unfold finiteEulerProduct
  simp

/-- Minimal analytic gate: the convergence region. -/
structure AnalyticGate (P : PrimeGasPartition) where
  β : ℂ
  re_gt_one : 1 < β.re
  inDomain : P.convergenceDomain β

/-- Stronger gate when downstream arguments divide by the readouts. -/
structure NonvanishingGate (P : PrimeGasPartition) where
  gate : AnalyticGate P
  partition_ne_zero : P.partitionFunction gate.β ≠ 0
  eulerProduct_ne_zero : P.eulerProduct gate.β ≠ 0

/--
Prime-weight specialization.

This is the formal statement that an abstract carrier is actually the
prime Euler-product carrier.
-/
structure PrimeWeightSpecialization (P : PrimeGasPartition) where
  support : Set Nat.Primes
  support_eq_univ : support = Set.univ
  partitionFunction_eq_tprod :
    ∀ s : ℂ,
      P.partitionFunction s =
        ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹
  eulerProduct_eq_tprod :
    ∀ s : ℂ,
      P.eulerProduct s =
        ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹

lemma eulerProduct_of_primeWeights
    {P : PrimeGasPartition} (hP : PrimeWeightSpecialization P) (s : ℂ) :
    P.eulerProduct s =
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ :=
  hP.eulerProduct_eq_tprod s

/--
Abstract bridge: any carrier specialized to the full prime Euler product
has zeta as its invariant partition readout on `Re(s) > 1`.
-/
theorem partitionFunction_eq_riemannZeta_of_primeWeights
    {P : PrimeGasPartition} (hP : PrimeWeightSpecialization P)
    {s : ℂ} (hs : 1 < s.re) :
    P.partitionFunction s = riemannZeta s := by
  rw [hP.partitionFunction_eq_tprod s]
  exact riemannZeta_eulerProduct_tprod hs

theorem eulerProduct_eq_riemannZeta_of_primeWeights
    {P : PrimeGasPartition} (hP : PrimeWeightSpecialization P)
    {s : ℂ} (hs : 1 < s.re) :
    P.eulerProduct s = riemannZeta s := by
  rw [hP.eulerProduct_eq_tprod s]
  exact riemannZeta_eulerProduct_tprod hs

/-- The canonical prime-gas carrier. -/
def zetaPrimeGas : PrimeGasPartition where
  primeIndex := Nat.Primes
  prime := fun p => p
  prime_isPrime := fun p => p.2
  energyOfPrime := fun p => Real.log (p : ℝ)
  convergenceDomain := fun s => 1 < s.re
  partitionFunction := fun s =>
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹
  eulerProduct := fun s =>
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹

@[simp]
lemma zetaPrimeGas_energyOfPrime (p : Nat.Primes) :
    zetaPrimeGas.energyOfPrime p = Real.log (p : ℝ) := rfl

@[simp]
lemma zetaPrimeGas_convergenceDomain (s : ℂ) :
    zetaPrimeGas.convergenceDomain s ↔ 1 < s.re := Iff.rfl

@[simp]
lemma zetaPrimeGas_partitionFunction (s : ℂ) :
    zetaPrimeGas.partitionFunction s =
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := rfl

@[simp]
lemma zetaPrimeGas_eulerProduct (s : ℂ) :
    zetaPrimeGas.eulerProduct s =
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := rfl

/-- The canonical carrier is specialized to the full prime Euler product. -/
def zetaPrimeGasSpecialization :
    PrimeWeightSpecialization zetaPrimeGas where
  support := Set.univ
  support_eq_univ := rfl
  partitionFunction_eq_tprod := by
    intro s
    rfl
  eulerProduct_eq_tprod := by
    intro s
    rfl

/--
Klein/Hestenes readout theorem:
the multiplicative prime carrier has scalar invariant `riemannZeta`
inside the convergence gate.
-/
theorem zetaPrimeGas_partitionFunction_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    zetaPrimeGas.partitionFunction s = riemannZeta s :=
  partitionFunction_eq_riemannZeta_of_primeWeights
    zetaPrimeGasSpecialization hs

theorem zetaPrimeGas_eulerProduct_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    zetaPrimeGas.eulerProduct s = riemannZeta s :=
  eulerProduct_eq_riemannZeta_of_primeWeights
    zetaPrimeGasSpecialization hs

/-- Minimal convergence gate for the canonical carrier. -/
def zetaPrimeGasAnalyticGate {s : ℂ} (hs : 1 < s.re) :
    AnalyticGate zetaPrimeGas where
  β := s
  re_gt_one := hs
  inDomain := by
    simpa [zetaPrimeGas] using hs

/-- Strong nonvanishing gate for the canonical carrier. -/
def zetaPrimeGasNonvanishingGate {s : ℂ} (hs : 1 < s.re) :
    NonvanishingGate zetaPrimeGas where
  gate := zetaPrimeGasAnalyticGate hs
  partition_ne_zero := by
    change zetaPrimeGas.partitionFunction s ≠ 0
    rw [zetaPrimeGas_partitionFunction_eq_riemannZeta hs]
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
  eulerProduct_ne_zero := by
    change zetaPrimeGas.eulerProduct s ≠ 0
    rw [zetaPrimeGas_eulerProduct_eq_riemannZeta hs]
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)

end PrimeGasPartition

/--
Preferred bridge name.

The reciprocal Euler factors multiply to `ζ(s)`.
-/
theorem weyl_denominator_limit_eq_zeta
    {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s := by
  simpa using riemannZeta_eulerProduct_tprod hs

/--
Compatibility alias for the proposed lane name.

Despite the name, the right-hand side is `ζ(s)`, not `ζ(s)⁻¹`.
-/
theorem weyl_denominator_limit_eq_inv_zeta
    {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s := by
  simpa using weyl_denominator_limit_eq_zeta hs

end Experimental.WeylDenominatorPrimeCutoff

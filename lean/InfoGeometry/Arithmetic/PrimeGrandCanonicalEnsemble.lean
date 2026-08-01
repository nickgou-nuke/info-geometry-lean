import Mathlib.Tactic
import InfoGeometry.GrandCanonical.ResponseMatrix
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

Finite grand-canonical ensemble on the prime-occupation state space.

This module specializes the existing finite grand-canonical core to a finite
prime cutoff:

* states are square-free prime subsets, represented as elements of
  `P.primes.powerset`;
* energy is a prime-weight sum over occupied primes;
* number is the occupied-mode cardinality;
* partition, Gibbs weights, potential, and response theorems come from the
  generic grand-canonical model.

The file remains finite and theorem-safe.  It does not claim any infinite
limit, thermodynamic completion, or RH statement.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## 1. Finite prime grand-canonical carrier -/

/--
Finite prime-occupation states.

The carrier is the powerset subtype, so Lean sees it as a finite type directly.
-/
@[rep_depth thermo]
abbrev PrimeState (P : PrimeRegister) :=
  {S : Finset ℕ // S ∈ P.primes.powerset}

instance (P : PrimeRegister) : Fintype (PrimeState P) := by
  infer_instance

instance (P : PrimeRegister) : Nonempty (PrimeState P) := by
  refine ⟨⟨∅, ?_⟩⟩
  simp

/-- The occupied prime set of a state. -/
@[rep_depth thermo]
def occupied {P : PrimeRegister} (S : PrimeState P) : Finset ℕ :=
  S.1

/-- Prime-weighted energy observable on a state. -/
@[rep_depth thermo]
def stateEnergy {P : PrimeRegister}
    (lam : ℕ → ℝ) (S : PrimeState P) : ℝ :=
  Finset.sum S.1 (fun p => lam p)

/-- Occupation-number observable on a state. -/
@[rep_depth thermo]
def stateNumber {P : PrimeRegister} (S : PrimeState P) : ℝ :=
  S.1.card

/-- The grand-canonical two-parameter data associated to a prime register and energy weight. -/
@[rep_depth thermo]
def primeGrandCanonicalParams (P : PrimeRegister) (energyWeight : ℕ → ℝ) :
    InfoGeometry.GrandCanonical.GrandCanonicalTwoParam (PrimeState P) where
  energy := stateEnergy energyWeight
  number := stateNumber

/-! ## 4. Finite Euler-product readout -/

/-- Finite Euler product associated to the prime grand-canonical packet. -/
@[rep_depth thermo]
def finiteEulerProduct (P : PrimeRegister) (energyWeight : ℕ → ℝ) (β μ : ℝ) : ℝ :=
  ∏ p ∈ P.primes, (1 + Real.exp (-β * (energyWeight p - μ)))

/--
A finite occupied-prime Gibbs factor is the product of its one-prime activities.
-/
lemma exp_neg_beta_stateEnergy_sub_mu_card
    (lam : ℕ → ℝ) (β μ : ℝ) (S : Finset ℕ) :
    Real.exp (-β * ((∑ p ∈ S, lam p) - μ * (S.card : ℝ))) =
      ∏ p ∈ S, Real.exp (-β * (lam p - μ)) := by
  have hsum : (∑ p ∈ S, (lam p - μ)) = (∑ p ∈ S, lam p) - μ * (S.card : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have harg : -β * ((∑ p ∈ S, lam p) - μ * (S.card : ℝ)) =
      ∑ p ∈ S, -β * (lam p - μ) := by
    rw [← hsum]
    exact Finset.mul_sum S (fun p => lam p - μ) (-β)
  rw [harg, Real.exp_sum]

/--
The finite prime grand-canonical Gibbs partition is the finite Euler product
over one-prime occupation factors.
-/
theorem partition_eq_finiteEulerProduct (P : PrimeRegister) (energyWeight : ℕ → ℝ) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.partitionGC (primeGrandCanonicalParams P energyWeight) β μ =
      finiteEulerProduct P energyWeight β μ := by
  classical
  calc
    InfoGeometry.GrandCanonical.partitionGC (primeGrandCanonicalParams P energyWeight) β μ =
        ∑ S : PrimeState P,
          Real.exp (-β * ((∑ p ∈ S.1, energyWeight p) - μ * (S.1.card : ℝ))) := by
            rfl
    _ = ∑ S ∈ P.primes.powerset,
          Real.exp (-β * ((∑ p ∈ S, energyWeight p) - μ * (S.card : ℝ))) := by
            symm
            exact Finset.sum_subtype
              (s := P.primes.powerset)
              (p := fun S : Finset ℕ => S ∈ P.primes.powerset)
              (h := fun S => Iff.rfl)
              (f := fun S => Real.exp (-β * ((∑ p ∈ S, energyWeight p) - μ * (S.card : ℝ))))
    _ = ∑ S ∈ P.primes.powerset,
          ∏ p ∈ S, Real.exp (-β * (energyWeight p - μ)) := by
            refine Finset.sum_congr rfl ?_
            intro S _hS
            exact exp_neg_beta_stateEnergy_sub_mu_card energyWeight β μ S
    _ = finiteEulerProduct P energyWeight β μ := by
            exact (Finset.prod_one_add (s := P.primes)
              (f := fun p => Real.exp (-β * (energyWeight p - μ)))).symm

/-- The finite Massieu/log-partition potential is the logarithm of the Euler product. -/
@[simp, rep_depth thermo]
theorem potential_eq_log_finiteEulerProduct (P : PrimeRegister) (energyWeight : ℕ → ℝ) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.potentialGC (primeGrandCanonicalParams P energyWeight) β μ =
      Real.log (finiteEulerProduct P energyWeight β μ) := by
  change Real.log (InfoGeometry.GrandCanonical.partitionGC (primeGrandCanonicalParams P energyWeight) β μ) = Real.log (finiteEulerProduct P energyWeight β μ)
  rw [partition_eq_finiteEulerProduct]

/-! ## 5. Log-energy specialization -/

/-- The logarithmic prime-energy specialization `lam p = log p`. -/
@[rep_depth thermo]
def logPrimeEnergyWeight : ℕ → ℝ :=
  fun p => Real.log p

/--
The logarithmic prime Gibbs partition is the finite Euler product over
`1 + exp(-β(log p - μ))`.
-/
theorem logPrimePacket_partition_eq_finiteEulerProduct (P : PrimeRegister) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.partitionGC (primeGrandCanonicalParams P logPrimeEnergyWeight) β μ =
      ∏ p ∈ P.primes, (1 + Real.exp (-β * (Real.log (p : ℝ) - μ))) := by
  simpa [logPrimeEnergyWeight, finiteEulerProduct] using
    partition_eq_finiteEulerProduct P logPrimeEnergyWeight β μ

/-- The logarithmic prime Massieu potential is the log of the finite Euler product. -/
@[simp, rep_depth thermo]
theorem logPrimePacket_potential_eq_log_finiteEulerProduct (P : PrimeRegister) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.potentialGC (primeGrandCanonicalParams P logPrimeEnergyWeight) β μ =
      Real.log (∏ p ∈ P.primes, (1 + Real.exp (-β * (Real.log (p : ℝ) - μ)))) := by
  rw [potential_eq_log_finiteEulerProduct]
  simp [logPrimeEnergyWeight, finiteEulerProduct]

end InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Canonical.HolographicEntanglementSymmetry
import InfoGeometry.Projective.KleinQuadricMonodromy

/-!
# InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock

Finite parafermion grand-canonical owner file.

This module keeps the algebra honest:

* `κ`-local occupation is the finite geometric series `∑_{j < κ} x^j`;
* `κ = 2` collapses to the fermionic square-free factor `1 + x`;
* `κ = 3` gives the `Z₃` local factor `1 + x + x^2`;
* finite products define the grand-canonical partition, Massieu potential,
  grand potential, and Boltzmann entropy readout;
* the positive-branch time clock theorem is re-used from the existing
  holographic lane.

No analytic continuation or continuum parafermion QFT claim is made here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock

open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.Arithmetic.PrimeSuperalgebra
open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData
open InfoGeometry.Canonical.TrialitySpin8Permutations
open InfoGeometry.Canonical.HolographicEntanglementSymmetry
open InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-- The `κ`-local parafermion occupation factor. -/
def parafermionLocalFactor (κ : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range κ) (fun j => x ^ j)

/-- Microscopic occupation probability for the local `κ`-truncated mode. -/
def stateProbability (κ : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / parafermionLocalFactor κ x

/-- Microscopic surprisal of the `n`-th local state. -/
def stateSurprisal (κ : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  -Real.log (stateProbability κ x n)

/--
The microscopic state surprisal splits into the Massieu normalization and the
logarithmic occupation weight.
-/
theorem stateSurprisal_eq_massieu_sub_logWeight
    (κ : ℕ) (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hQ : 0 < parafermionLocalFactor κ x) :
    stateSurprisal κ x n =
      Real.log (parafermionLocalFactor κ x) - n * Real.log x := by
  unfold stateSurprisal stateProbability
  rw [Real.log_div (pow_pos hx n).ne' hQ.ne', Real.log_pow x n]
  ring

/--
Historical compatibility name for the state-surprisal decomposition.

Its conclusion is a negative-log probability identity, not a Boltzmann
macrostate-multiplicity theorem. The retained legacy name is not a semantic
identification with Boltzmann macroentropy.
-/
theorem stateSurprisal_eq_boltzmannEntropy
    (κ : ℕ) (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hQ : 0 < parafermionLocalFactor κ x) :
    stateSurprisal κ x n =
      Real.log (parafermionLocalFactor κ x) - n * Real.log x :=
  stateSurprisal_eq_massieu_sub_logWeight κ x n hx hQ

/-- The local occupation law is the geometric weight normalized by the `κ`-sum. -/
theorem stateProbability_eq_kappa_normalized_weight (κ : ℕ) (x : ℝ) (n : ℕ) :
    stateProbability κ x n = x ^ n / Finset.sum (Finset.range κ) (fun j => x ^ j) := by
  rfl

/-- The local log-partition function. -/
def parafermionMassieu (κ : ℕ) (x : ℝ) : ℝ :=
  Real.log (parafermionLocalFactor κ x)

/-- Finite local expected occupation number. -/
def localExpectedOccupation (κ : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range κ) (fun n => (n : ℝ) * stateProbability κ x n)

/-- Finite local Shannon/Boltzmann entropy of the truncated mode. -/
def localShannonEntropy (κ : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range κ) (fun n => stateProbability κ x n * stateSurprisal κ x n)

/-- The corresponding scalar grand potential readout. -/
def parafermionGrandPotential (β : ℝ) (κ : ℕ) (x : ℝ) : ℝ :=
  -β⁻¹ * parafermionMassieu κ x

/-- The geometric calibration potential. -/
def Q_kappa (κ : ℕ) (x : ℝ) : ℝ :=
  parafermionLocalFactor κ x

/-- The geometric potential is exactly the Massieu potential. -/
theorem ln_Q_is_massieu (κ : ℕ) (x : ℝ) :
    Real.log (Q_kappa κ x) = parafermionMassieu κ x := by
  rfl

/-- The grand potential is `-β⁻¹ log Q_κ`. -/
theorem parafermionGrandPotential_eq_neg_inv_beta_mul_log_Q
    (β : ℝ) (κ : ℕ) (x : ℝ) :
    parafermionGrandPotential β κ x = -β⁻¹ * Real.log (Q_kappa κ x) := by
  rfl

/-- The local factor is the geometric sum in standard `Finset.range` form. -/
theorem parafermionLocalFactor_eq_geomSum (κ : ℕ) (x : ℝ) :
    parafermionLocalFactor κ x = Finset.sum (Finset.range κ) (fun j => x ^ j) := by
  rfl

/-- Increasing `κ` adds exactly one more occupation term to the local factor. -/
theorem parafermionLocalFactor_succ (κ : ℕ) (x : ℝ) :
    parafermionLocalFactor (κ + 1) x = parafermionLocalFactor κ x + x ^ κ := by
  simp [parafermionLocalFactor, Finset.sum_range_succ]

/-- Geometric-series quotient form. -/
theorem parafermionLocalFactor_eq_div (κ : ℕ) (x : ℝ) (hx : x ≠ 1) :
    parafermionLocalFactor κ x = (1 - x ^ κ) / (1 - x) := by
  have hmul : parafermionLocalFactor κ x * (1 - x) = 1 - x ^ κ := by
    simpa [parafermionLocalFactor, mul_comm, mul_left_comm, mul_assoc] using
      geom_sum_mul_neg x κ
  have hden : (1 - x) ≠ 0 := sub_ne_zero.mpr (by intro h; exact hx h.symm)
  exact (eq_div_iff hden).2 hmul

/-- `κ = 2` gives the fermionic local factor `1 + x`. -/
theorem parafermionLocalFactor_two (x : ℝ) :
    parafermionLocalFactor 2 x = 1 + x := by
  simp [parafermionLocalFactor, Finset.sum_range_succ]

/-- For fermions, the probability law is exactly the `κ = 2` normalization. -/
theorem stateProbability_two (x : ℝ) (n : ℕ) :
    stateProbability 2 x n = x ^ n / (1 + x) := by
  simp [stateProbability, parafermionLocalFactor_two]

/-- `κ = 3` gives the `Z₃` local factor `1 + x + x^2`. -/
theorem parafermionLocalFactor_three (x : ℝ) :
    parafermionLocalFactor 3 x = 1 + x + x ^ 2 := by
  simp [parafermionLocalFactor, Finset.sum_range_succ, pow_two]

/-- For order-3 parafermions, the probability law is exactly the `κ = 3` normalization. -/
theorem stateProbability_three (x : ℝ) (n : ℕ) :
    stateProbability 3 x n = x ^ n / (1 + x + x ^ 2) := by
  simp [stateProbability, parafermionLocalFactor_three]

/-- Finite expected surprisal equals Massieu minus the weighted log-occupation term. -/
theorem localShannonEntropy_eq_massieu_sub_expectedOccupation_mul_log
    (κ : ℕ) (x : ℝ)
    (hx : 0 < x) (hQ : 0 < parafermionLocalFactor κ x) :
    localShannonEntropy κ x =
      parafermionMassieu κ x - localExpectedOccupation κ x * Real.log x := by
  unfold localShannonEntropy localExpectedOccupation parafermionMassieu
  calc
    Finset.sum (Finset.range κ) (fun n => stateProbability κ x n * stateSurprisal κ x n)
        = Finset.sum (Finset.range κ)
            (fun n =>
              stateProbability κ x n *
                (Real.log (parafermionLocalFactor κ x) - n * Real.log x)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [stateSurprisal_eq_massieu_sub_logWeight κ x n hx hQ]
    _ = Finset.sum (Finset.range κ)
          (fun n =>
            stateProbability κ x n * Real.log (parafermionLocalFactor κ x)
              - stateProbability κ x n * (n * Real.log x)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          ring
    _ = Finset.sum (Finset.range κ)
          (fun n => stateProbability κ x n * Real.log (parafermionLocalFactor κ x))
        - Finset.sum (Finset.range κ)
          (fun n => stateProbability κ x n * (n * Real.log x)) := by
          rw [Finset.sum_sub_distrib]
    _ = Real.log (parafermionLocalFactor κ x) * Finset.sum (Finset.range κ) (stateProbability κ x)
        - Finset.sum (Finset.range κ) (fun n => (n : ℝ) * stateProbability κ x n) * Real.log x := by
          congr 1
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
          · have hmul :
                Finset.sum (Finset.range κ) (fun n => stateProbability κ x n * (n * Real.log x))
                  = Finset.sum (Finset.range κ)
                      (fun n => ((n : ℝ) * stateProbability κ x n) * Real.log x) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                ring
            rw [hmul, ← Finset.sum_mul]
    _ = parafermionMassieu κ x - localExpectedOccupation κ x * Real.log x := by
          have hprob_sum : Finset.sum (Finset.range κ) (stateProbability κ x) = 1 := by
            unfold stateProbability parafermionLocalFactor
            have hden : Finset.sum (Finset.range κ) (fun i => x ^ i) ≠ 0 := by
              simpa using hQ.ne'
            rw [← Finset.sum_div]
            exact div_self hden
          simp [hprob_sum, localExpectedOccupation, parafermionMassieu]

/-- Prime-weight specialization of microscopic surprisal. -/
theorem stateSurprisal_eq_primeWeight_massieu_add_energy
    (κ : ℕ) (β : ℝ) (p n : ℕ)
    (hQ : 0 < parafermionLocalFactor κ (primeWeight β p)) :
    stateSurprisal κ (primeWeight β p) n =
      parafermionMassieu κ (primeWeight β p) + n * (β * primeEnergy p) := by
  have hx : 0 < primeWeight β p := by
    unfold primeWeight
    exact Real.exp_pos _
  rw [stateSurprisal_eq_massieu_sub_logWeight κ (primeWeight β p) n hx hQ]
  unfold parafermionMassieu primeWeight primeEnergy
  rw [Real.log_exp]
  ring

/-- The parafermion local factor tends to the bosonic geometric limit. -/
theorem tendsto_parafermionLocalFactor_atTop (x : ℝ) (hx : |x| < 1) :
    Filter.Tendsto (fun κ : ℕ => parafermionLocalFactor κ x) Filter.atTop (nhds ((1 - x)⁻¹)) := by
  have hs : Summable fun n : ℕ => x ^ n := summable_geometric_of_abs_lt_one hx
  simpa [parafermionLocalFactor, tsum_geometric_of_abs_lt_one hx] using
    hs.hasSum.tendsto_sum_nat

/--
Finite grand-canonical parafermion packet on a prime cutoff.

`weight` is the local occupation weight, for example `p ↦ z * p^(-β)` in the
prime grand-canonical specialization.
-/
structure PrimeParafermionGrandCanonicalPacket where
  cutoff : PrimeCutoff
  kappa : ℕ
  weight : ℕ → ℝ
  beta : ℝ
  mu : ℝ

namespace PrimeParafermionGrandCanonicalPacket

/-- Global finite parafermion partition function. -/
def partition (B : PrimeParafermionGrandCanonicalPacket) : ℝ :=
  ∏ p ∈ B.cutoff.primes, parafermionLocalFactor B.kappa (B.weight p)

/-- Massieu potential `ψ = log Ξ`. -/
def massieu (B : PrimeParafermionGrandCanonicalPacket) : ℝ :=
  Real.log B.partition

/-- Grand potential `Ω = -β⁻¹ log Ξ`. -/
def grandPotential (B : PrimeParafermionGrandCanonicalPacket) : ℝ :=
  -B.beta⁻¹ * B.massieu

/-- Grand-canonical surprisal readout in Massieu form. -/
def boltzmannEntropy (B : PrimeParafermionGrandCanonicalPacket) (U N : ℝ) : ℝ :=
  B.massieu + B.beta * (U - B.mu * N)

/-- The partition is the finite product of local parafermion factors. -/
theorem partition_eq_prod (B : PrimeParafermionGrandCanonicalPacket) :
    B.partition = ∏ p ∈ B.cutoff.primes, parafermionLocalFactor B.kappa (B.weight p) := by
  rfl

/-- The Massieu potential is the logarithm of the partition. -/
theorem massieu_eq_log_partition (B : PrimeParafermionGrandCanonicalPacket) :
    B.massieu = Real.log B.partition := by
  rfl

/-- The grand potential is `-β⁻¹` times the Massieu potential. -/
theorem grandPotential_eq_neg_inv_beta_mul_massieu
    (B : PrimeParafermionGrandCanonicalPacket) :
    B.grandPotential = -B.beta⁻¹ * B.massieu := by
  rfl

/-- The Boltzmann entropy is the standard Massieu correction formula. -/
theorem boltzmannEntropy_eq (B : PrimeParafermionGrandCanonicalPacket) (U N : ℝ) :
    B.boltzmannEntropy U N = B.massieu + B.beta * (U - B.mu * N) := by
  rfl

/-- `κ = 2` specialization: the prime packet becomes the fermionic square-free product. -/
theorem partition_two_eq_squarefreeProduct
    (B : PrimeParafermionGrandCanonicalPacket) :
    (PrimeParafermionGrandCanonicalPacket.partition (B := { B with kappa := 2 }))
      = ∏ p ∈ B.cutoff.primes, (1 + B.weight p) := by
  simp [PrimeParafermionGrandCanonicalPacket.partition, parafermionLocalFactor_two]

/-- `κ = 2` with negated local weights yields the Weyl denominator factor. -/
theorem partition_two_neg_eq_weylDenominator
    (B : PrimeParafermionGrandCanonicalPacket) :
    (PrimeParafermionGrandCanonicalPacket.partition (B := { B with kappa := 2, weight := fun p => -B.weight p }))
      = ∏ p ∈ B.cutoff.primes, (1 - B.weight p) := by
  simp [PrimeParafermionGrandCanonicalPacket.partition, parafermionLocalFactor_two, sub_eq_add_neg]

/-- `κ = 3` specialization: the local factor is `1 + x + x^2`. -/
theorem partition_three_local_factor
    (B : PrimeParafermionGrandCanonicalPacket) :
    ∀ p ∈ B.cutoff.primes, parafermionLocalFactor 3 (B.weight p) = 1 + B.weight p + (B.weight p)^2 := by
  intro p hp
  simpa using parafermionLocalFactor_three (B.weight p)

end PrimeParafermionGrandCanonicalPacket

/-- Fermionic square-free collapse through the existing prime-superalgebra lane. -/
theorem fermionicCollapse_eq_primeSuperalgebra
    (P : PrimeCutoff) (β : ℝ) :
    PrimeParafermionGrandCanonicalPacket.partition
      (B := { cutoff := P, kappa := 2, weight := primeWeight β, beta := β, mu := 0 })
      =
    finiteSquarefreeProduct P β := by
  simpa [PrimeParafermionGrandCanonicalPacket.partition, primeWeight]
    using (PrimeParafermionGrandCanonicalPacket.partition_two_eq_squarefreeProduct
      (B := { cutoff := P, kappa := 2, weight := primeWeight β, beta := β, mu := 0 }))

/-- The `κ = 2` prime parafermion packet equals the finite square-free fermion sum. -/
theorem fermionicCollapse_eq_squarefreePartitionSum
    (P : PrimeCutoff) (β : ℝ) :
    PrimeParafermionGrandCanonicalPacket.partition
      (B := { cutoff := P, kappa := 2, weight := primeWeight β, beta := β, mu := 0 })
      =
    finiteFermionicSquarefreePartition P β := by
  rw [fermionicCollapse_eq_primeSuperalgebra]
  exact (finiteFermionicSquarefreePartition_eq_product P β).symm

/-- Fermionic square-free partition equals the signed supertrace after negating local weights. -/
theorem signedCollapse_eq_primeSuperalgebra
    (P : PrimeCutoff) (β : ℝ) :
    PrimeParafermionGrandCanonicalPacket.partition
      (B := { cutoff := P, kappa := 2, weight := fun p => -primeWeight β p, beta := β, mu := 0 })
      =
    finitePrimeDenominator P β := by
  simpa [PrimeParafermionGrandCanonicalPacket.partition, primeWeight,
    finitePrimeDenominator, sub_eq_add_neg]
    using (PrimeParafermionGrandCanonicalPacket.partition_two_neg_eq_weylDenominator
      (B := { cutoff := P, kappa := 2, weight := primeWeight β, beta := β, mu := 0 }))

/-- The signed `κ = 2` collapse equals the finite prime supertrace. -/
theorem signedCollapse_eq_primeSupertrace
    (P : PrimeCutoff) (β : ℝ) :
    PrimeParafermionGrandCanonicalPacket.partition
      (B := { cutoff := P, kappa := 2, weight := fun p => -primeWeight β p, beta := β, mu := 0 })
      =
    finitePrimeSupertrace P β := by
  rw [signedCollapse_eq_primeSuperalgebra]
  exact (finitePrimeSupertrace_eq_denominator P β).symm

/-- The local `Z₃` packet specialization is the expected trinomial factor. -/
theorem z3_localFactor_eq_trinomial
    (B : PrimeParafermionGrandCanonicalPacket) (p : ℕ) :
    parafermionLocalFactor 3 (B.weight p) = 1 + B.weight p + (B.weight p) ^ 2 := by
  simpa using parafermionLocalFactor_three (B.weight p)

/-- The positive-branch thermal-time theorem is reused unchanged. -/
theorem positiveBranchThermalTime
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector}
    {n N : ℕ} {A : EndH E}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      subtreeEntropy n = minimalSurfaceArea n / (4 * effectiveNewtonConstant) := by
  exact positive_branch_time_clock_theorem (B := B) P

end InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock

import InfoGeometry.Arithmetic.PrimeBitLattice
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.Inference.GrandCanonicalGibbsFluctuationBridge
import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Thermodynamics.FiniteGibbsRelative

/-!
# Finite Gibbs readout of the prime-bit lattice

The prime-bit partition is the finite Gibbs partition of the powerset data
carrier with the logarithmic prime-bit energy.  This file only transports the
existing finite Gibbs API to that carrier; it makes no infinite-product or
analytic claim.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeBitFiniteGibbsBridge

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitLattice
open InfoGeometry.GrandCanonical
open InfoGeometry.Inference
open InfoGeometry.Inference.FiniteGibbs
open InfoGeometry.Thermodynamics.FiniteGibbsRelative

/-- The finite powerset carrier underlying a prime-bit lattice. -/
abbrev PrimeBitSubset (L : PrimeBitLattice) :=
  {S : Finset ℕ // S ∈ L.primes.powerset}

noncomputable instance primeBitSubsetFintype (L : PrimeBitLattice) :
    Fintype (PrimeBitSubset L) :=
  Fintype.ofFinite (PrimeBitSubset L)

instance primeBitSubsetNonempty (L : PrimeBitLattice) :
    Nonempty (PrimeBitSubset L) :=
  ⟨⟨∅, by simp⟩⟩

/-- The logarithmic energy model on the finite powerset carrier. -/
def primeBitGibbsModel (L : PrimeBitLattice) :
    Model (Data := PrimeBitSubset L) (Theta := Unit) :=
  ⟨fun S _ => primeBitEnergy L S.1⟩

/-- The same logarithmic energy as a native grand-canonical parameter. -/
def primeBitGrandCanonicalParams (L : PrimeBitLattice) :
    GrandCanonicalParams (PrimeBitSubset L) :=
  ⟨fun S => primeBitEnergy L S.1⟩

/-- Cartan parameters presenting the same prime-bit Gibbs law in the finite
Massieu owner.  This is a readout bridge, not a new state carrier. -/
def primeBitCartanParameters (L : PrimeBitLattice) (β : ℝ) :
    FiniteTemperature (PrimeBitSubset L) :=
  fun S => -β * primeBitEnergy L S.1

theorem primeBit_relativeEntropy_eq_finiteGibbsRelativeEntropy
    (L : PrimeBitLattice) (β γ : ℝ) :
    relativeEntropy
        (primeBitCartanParameters L β)
        (primeBitCartanParameters L γ) =
      InfoGeometry.Probability.FiniteGibbsVariational.finiteRelativeEntropy
        (GrandCanonical.gibbsWeight
          (primeBitGrandCanonicalParams L) β)
         (GrandCanonical.gibbsWeight
           (primeBitGrandCanonicalParams L) γ) := by
  rw [relativeEntropy_eq_normalizedFiniteRelativeEntropy
    (primeBitCartanParameters L β)
    (primeBitCartanParameters L γ)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)
      (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)]
  rfl

/-- The prime-bit relative deviance is the native Massieu-Bregman gap. -/
theorem primeBit_relativeEntropy_eq_massieuBregman
    (L : PrimeBitLattice) (β γ : ℝ) :
    relativeEntropy
        (primeBitCartanParameters L β)
        (primeBitCartanParameters L γ) =
      massieuBregman
        (primeBitCartanParameters L β)
        (primeBitCartanParameters L γ) := by
  exact relativeEntropy_eq_massieuBregman
    (primeBitCartanParameters L β)
    (primeBitCartanParameters L γ)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)

/-- Nonnegativity of the transported prime-bit finite relative entropy. -/
theorem primeBit_relativeEntropy_nonneg
    (L : PrimeBitLattice) (β γ : ℝ) :
    0 ≤ relativeEntropy
      (primeBitCartanParameters L β)
      (primeBitCartanParameters L γ) := by
  exact relativeEntropy_nonneg
    (primeBitCartanParameters L β)
    (primeBitCartanParameters L γ)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)

/-- Equality is precisely the common additive Cartan-gauge orbit. -/
theorem primeBit_relativeEntropy_eq_zero_iff_common_shift
    (L : PrimeBitLattice) (β γ : ℝ) :
    relativeEntropy
        (primeBitCartanParameters L β)
        (primeBitCartanParameters L γ) = 0 ↔
      ∃ c : ℝ, ∀ S : PrimeBitSubset L,
        primeBitCartanParameters L γ S =
          primeBitCartanParameters L β S + c := by
  exact relativeEntropy_eq_zero_iff_common_shift
    (primeBitCartanParameters L β)
    (primeBitCartanParameters L γ)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)

/-- Strict finite Gibbs dissipation away from the common Cartan gauge orbit. -/
theorem primeBit_relativeEntropy_pos_of_not_common_shift
    (L : PrimeBitLattice) (β γ : ℝ)
    (hnot : ¬ ∃ c : ℝ, ∀ S : PrimeBitSubset L,
      primeBitCartanParameters L γ S =
        primeBitCartanParameters L β S + c) :
    0 < relativeEntropy
      (primeBitCartanParameters L β)
      (primeBitCartanParameters L γ) := by
  exact relativeEntropy_pos_of_not_common_shift
    (primeBitCartanParameters L β)
    (primeBitCartanParameters L γ)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)
    (InfoGeometry.Algebraic.CartanExponentialFamily.Z_pos _)
    hnot

theorem primeBitGrandCanonical_partition_eq_fermionic
    (L : PrimeBitLattice) (β : ℝ) :
    GrandCanonical.partition (primeBitGrandCanonicalParams L) β =
      primeBitFermionicPartition L β := by
  classical
  change
    (∑ S : PrimeBitSubset L,
      Real.exp (-β * primeBitEnergy L S.1)) =
      Finset.sum L.primes.powerset
        (fun S => Real.exp (-β * primeBitEnergy L S))
  have hpowerset : ∀ S : Finset ℕ,
      S ∈ L.primes.powerset ↔ S ∈ L.primes.powerset := by
    intro S
    rfl
  symm
  rw [Finset.sum_subtype (F := primeBitSubsetFintype L)
    L.primes.powerset hpowerset
    (fun S => Real.exp (-β * primeBitEnergy L S))]

/-- The finite grand-canonical mean energy transported to the powerset
    readout. -/
theorem primeBitGrandCanonical_mean_eq_fermionic_weighted_energy
    (L : PrimeBitLattice) (β : ℝ) :
    GrandCanonical.mean (primeBitGrandCanonicalParams L) β =
      ∑ S ∈ L.primes.powerset,
        (Real.exp (-β * primeBitEnergy L S) /
          primeBitFermionicPartition L β) * primeBitEnergy L S := by
  classical
  change
    (∑ S : PrimeBitSubset L,
      GrandCanonical.gibbsWeight
          (primeBitGrandCanonicalParams L) β S *
        primeBitEnergy L S.1) = _
  simp_rw [InfoGeometry.GrandCanonical.gibbsWeight]
  rw [primeBitGrandCanonical_partition_eq_fermionic]
  symm
  rw [Finset.sum_subtype (F := primeBitSubsetFintype L)
    L.primes.powerset
    (show ∀ S : Finset ℕ,
      S ∈ L.primes.powerset ↔ S ∈ L.primes.powerset from fun _ => Iff.rfl)
    (fun S =>
      (Real.exp (-β * primeBitEnergy L S) /
        primeBitFermionicPartition L β) * primeBitEnergy L S)]
  rfl

theorem primeBitGibbs_partition_eq_fermionic
    (L : PrimeBitLattice) (ε : ℝ) :
    partitionFunction (primeBitGibbsModel L) () ε =
      primeBitFermionicPartition L ε⁻¹ := by
  classical
  change
    (∑ S : PrimeBitSubset L,
      Real.exp (-primeBitEnergy L S.1 / ε)) =
      Finset.sum L.primes.powerset
        (fun S => Real.exp (-ε⁻¹ * primeBitEnergy L S))
  have hpowerset : ∀ S : Finset ℕ,
      S ∈ L.primes.powerset ↔ S ∈ L.primes.powerset := by
    intro S
    rfl
  symm
  rw [Finset.sum_subtype (F := primeBitSubsetFintype L)
    L.primes.powerset hpowerset
    (fun S => Real.exp (-ε⁻¹ * primeBitEnergy L S))]
  change
    (∑ S : PrimeBitSubset L,
      Real.exp (-ε⁻¹ * primeBitEnergy L S.1)) =
      ∑ S : PrimeBitSubset L,
        Real.exp (-primeBitEnergy L S.1 / ε)
  apply Fintype.sum_congr
  intro S
  congr 1
  rw [div_eq_mul_inv]
  ring

theorem primeBitGibbs_weight_eq_fermionic
    (L : PrimeBitLattice) (ε : ℝ) (S : PrimeBitSubset L) :
    weight (primeBitGibbsModel L) () ε S =
      Real.exp (-ε⁻¹ * primeBitEnergy L S.1) /
        primeBitFermionicPartition L ε⁻¹ := by
  change
    Real.exp (-primeBitEnergy L S.1 / ε) /
        partitionFunction (primeBitGibbsModel L) () ε =
      Real.exp (-ε⁻¹ * primeBitEnergy L S.1) /
        primeBitFermionicPartition L ε⁻¹
  rw [primeBitGibbs_partition_eq_fermionic]
  congr 2
  rw [div_eq_mul_inv]
  ring

theorem primeBitGrandCanonical_potential_eq_fermionic
    (L : PrimeBitLattice) (β : ℝ) :
    GrandCanonical.potential (primeBitGrandCanonicalParams L) β =
      Real.log (primeBitFermionicPartition L β) := by
  unfold GrandCanonical.potential
  rw [primeBitGrandCanonical_partition_eq_fermionic]

theorem primeBitGrandCanonical_potential_eq_sum_local_log
    (L : PrimeBitLattice) (β : ℝ) :
    GrandCanonical.potential (primeBitGrandCanonicalParams L) β =
      ∑ p ∈ L.primes,
        Real.log (1 + Real.exp (-β * Real.log p)) := by
  rw [primeBitGrandCanonical_potential_eq_fermionic,
    primeBitFermionicPartition_eq_factorizedProduct]
  have hne : ∀ p ∈ L.primes,
      (1 + Real.exp (-β * Real.log p)) ≠ 0 := by
    intro p hp
    have hpos : 0 < (1 : ℝ) + Real.exp (-β * Real.log p) := by
      exact add_pos_of_pos_of_nonneg zero_lt_one (Real.exp_pos _).le
    exact hpos.ne'
  rw [Real.log_prod hne]

theorem primeBitGibbs_freeEnergy_eq_fermionic
    (L : PrimeBitLattice) (ε : ℝ) :
    freeEnergy (primeBitGibbsModel L) () ε =
      -ε * Real.log (primeBitFermionicPartition L ε⁻¹) := by
  unfold freeEnergy
  rw [primeBitGibbs_partition_eq_fermionic]

theorem primeBitTemperatureSusceptibility_eq_weightedVariance
    (L : PrimeBitLattice) (ε : ℝ) :
    temperatureSusceptibility
        (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε =
      weightedVariance
        (GrandCanonical.gibbsWeight
          (primeBitGrandCanonicalParams L) ε⁻¹)
        (fun S : PrimeBitSubset L => primeBitEnergy L S.1) := by
  exact temperatureSusceptibility_eq_weightedVariance
    (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε

theorem primeBitTemperatureSusceptibility_nonneg
    (L : PrimeBitLattice) (ε : ℝ) :
    0 ≤ temperatureSusceptibility
      (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε := by
  exact temperatureSusceptibility_nonneg
    (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε

theorem primeBitTemperatureSusceptibility_eq_zero_iff
    (L : PrimeBitLattice) (ε : ℝ) :
    temperatureSusceptibility
        (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε = 0 ↔
      ∀ S : PrimeBitSubset L,
        primeBitEnergy L S.1 =
          GrandCanonical.mean
            (primeBitGrandCanonicalParams L) ε⁻¹ := by
  exact temperatureSusceptibility_eq_zero_iff
    (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε

theorem primeBitTemperatureSusceptibility_pos_of_two_distinct_primes
    (L : PrimeBitLattice) (ε : ℝ)
    {p q : ℕ} (hp : p ∈ L.primes) (hq : q ∈ L.primes) (hpq : p ≠ q) :
    0 < temperatureSusceptibility
      (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε := by
  have hpp : Nat.Prime p := L.isPrime p hp
  have hqp : Nat.Prime q := L.isPrime q hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hlog_ne : Real.log (p : ℝ) ≠ Real.log (q : ℝ) := by
    intro hlog
    have hexp := congrArg Real.exp hlog
    have hpq_real : (p : ℝ) = (q : ℝ) := by
      simpa [Real.exp_log hp0, Real.exp_log hq0] using hexp
    exact hpq (by exact_mod_cast hpq_real)
  let Sp : PrimeBitSubset L :=
    ⟨{p}, by simp [hp]⟩
  let Sq : PrimeBitSubset L :=
    ⟨{q}, by simp [hq]⟩
  have henergy_ne : primeBitEnergy L Sp.1 ≠
      primeBitEnergy L Sq.1 := by
    simpa [Sp, Sq, primeBitEnergy] using hlog_ne
  have hzero_ne : temperatureSusceptibility
      (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε ≠ 0 := by
    intro hzero
    have hall :=
      (primeBitTemperatureSusceptibility_eq_zero_iff L ε).mp hzero
    have hSp := hall Sp
    have hSq := hall Sq
    exact henergy_ne (hSp.trans hSq.symm)
  have hnonneg := primeBitTemperatureSusceptibility_nonneg L ε
  exact lt_of_le_of_ne hnonneg (fun h => hzero_ne h.symm)

end InfoGeometry.Arithmetic.PrimeBitFiniteGibbsBridge

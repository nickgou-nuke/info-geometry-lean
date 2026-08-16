import InfoGeometry.Arithmetic.PrimeBitLattice
import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.Inference.GrandCanonicalGibbsFluctuationBridge
import InfoGeometry.GrandCanonical.Core

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
  fun S _ => primeBitEnergy L S.1

/-- The same logarithmic energy as a native grand-canonical parameter. -/
def primeBitGrandCanonicalParams (L : PrimeBitLattice) :
    GrandCanonicalParams (PrimeBitSubset L) :=
  fun S => primeBitEnergy L S.1

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

theorem primeBitGrandCanonical_weight_eq_fermionic
    (L : PrimeBitLattice) (β : ℝ) (S : PrimeBitSubset L) :
    GrandCanonical.gibbsWeight (primeBitGrandCanonicalParams L) β S =
      Real.exp (-β * primeBitEnergy L S.1) /
        GrandCanonical.partition (primeBitGrandCanonicalParams L) β := by
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
  congr 1
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
  unfold temperatureSusceptibility
  exact grandCanonicalVariance_eq_weightedVariance
    (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε⁻¹

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
            (fun S : PrimeBitSubset L => primeBitEnergy L S.1) ε⁻¹ := by
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

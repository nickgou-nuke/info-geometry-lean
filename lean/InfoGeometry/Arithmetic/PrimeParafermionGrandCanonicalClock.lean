import Mathlib
import InfoGeometry.Potential.Thermo
import InfoGeometry.Information.DeRhamScore
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Arithmetic.PhysicsRiemannHypothesisFinite
import InfoGeometry.Projective.KleinQuadricMonodromy

/-!
# InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock

Unified finite owner surface for bosonic, fermionic, and finite-order
parafermionic prime grand-canonical factors together with a conservative
`log Q` / `d log Q` clock calibration.

Closed content in this file:

* grand-canonical prime activity `x_p = z p^{-s}`;
* bosonic, fermionic, signed-supertrace, and order-`κ` parafermion local factors;
* Massieu/log-generating potential, free-energy, grand-potential, and Boltzmann
  entropy readouts for the finite partition;
* calibration of a supplied `d log Q` one-form to the de Rham pole form `dz / z`,
  yielding the winding/holonomy clock;
* finite two-prime `{2,3}` readbacks re-exported from the existing arithmetic
  owner file.

This file does **not** claim an infinite parafermion Euler product theorem,
analytic continuation, RH, or a native differential formula identifying the
actual derivative of the finite partition with the de Rham pole form.  The
`d log Q` bridge is a supplied calibration packet.
-/

noncomputable section

open scoped BigOperators

namespace PrimeParafermionGrandCanonicalClock

open InfoGeometry.Arithmetic.PrimeSuperalgebra
open InfoGeometry.Arithmetic.PhysicsRiemannHypothesisFinite
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
open InfoGeometry.LogPotential

/-- Grand-canonical prime activity `x_p = z p^{-s}`. -/
def grandComplexPrimeWeight
    (z s : ℂ)
    (p : Nat.Primes) : ℂ :=
  z * complexPrimeWeight s p

/-- Finite occupancy local factor `1 + x + ⋯ + x^(κ-1)`. -/
def finiteParafermionLocalFactor
    (κ : ℕ)
    (x : ℂ) : ℂ :=
  ∑ j ∈ Finset.range κ, x ^ j

/-- Finite grand-canonical parafermion partition over a prime cutoff. -/
def finiteGrandParafermionPartition
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) : ℂ :=
  ∏ p ∈ S, finiteParafermionLocalFactor κ (grandComplexPrimeWeight z s p)

/-- Finite grand-canonical bosonic partition. -/
def finiteGrandBosonPartition
    (S : Finset Nat.Primes)
    (z s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - grandComplexPrimeWeight z s p)⁻¹

/-- Finite grand-canonical signed fermionic supertrace. -/
def finiteGrandSignedFermionSupertrace
    (S : Finset Nat.Primes)
    (z s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - grandComplexPrimeWeight z s p)

/-- Finite grand-canonical unsigned fermionic partition. -/
def finiteGrandFermionPartition
    (S : Finset Nat.Primes)
    (z s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 + grandComplexPrimeWeight z s p)

/-- Finite grand-canonical order-3 parafermion partition. -/
def finiteGrandParafermion3Partition
    (S : Finset Nat.Primes)
    (z s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 + grandComplexPrimeWeight z s p + (grandComplexPrimeWeight z s p) ^ 2)

/-- Log-generating / Massieu potential of the finite parafermion partition. -/
def parafermionMassieu
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) : ℂ :=
  Complex.log (finiteGrandParafermionPartition S z s κ)

/-- Free-energy readout `F = -log Ξ`. -/
def parafermionFreeEnergy
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) : ℂ :=
  -parafermionMassieu S z s κ

/-- Grand-potential readout `Ω = -s⁻¹ log Ξ`. -/
def parafermionGrandPotential
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) : ℂ :=
  -s⁻¹ * parafermionMassieu S z s κ

/-- Boltzmann entropy readout `S_B = Ψ + β (U - μN)`. -/
def boltzmannEntropyFromMassieu
    (massieu beta energy chemicalPotential particleNumber : ℂ) : ℂ :=
  massieu + beta * (energy - chemicalPotential * particleNumber)

/-- Grand-canonical microstate surprisal `-log p_i` in Massieu form. -/
def grandCanonicalSurprisal
    (massieu beta energy chemicalPotential particleNumber : ℂ) : ℂ :=
  beta * (energy - chemicalPotential * particleNumber) + massieu

/-- Weighted expected surprisal over a finite state space. -/
def expectedSurprisal
    {ι : Type*} (states : Finset ι)
    (weight : ι → ℂ)
    (surprisal : ι → ℂ) : ℂ :=
  ∑ i ∈ states, weight i * surprisal i

/-- Shannon/von-Neumann-style finite entropy readout as expected surprisal. -/
def shannonEntropyFromSurprisal
    {ι : Type*} (states : Finset ι)
    (weight : ι → ℂ)
    (surprisal : ι → ℂ) : ℂ :=
  expectedSurprisal states weight surprisal

@[simp]
theorem finiteParafermionLocalFactor_zero
    (x : ℂ) :
    finiteParafermionLocalFactor 0 x = 0 := by
  simp [finiteParafermionLocalFactor]

@[simp]
theorem finiteParafermionLocalFactor_one
    (x : ℂ) :
    finiteParafermionLocalFactor 1 x = 1 := by
  simp [finiteParafermionLocalFactor]

@[simp]
theorem finiteParafermionLocalFactor_two
    (x : ℂ) :
    finiteParafermionLocalFactor 2 x = 1 + x := by
  simp [finiteParafermionLocalFactor, add_comm]

@[simp]
theorem finiteParafermionLocalFactor_three
    (x : ℂ) :
    finiteParafermionLocalFactor 3 x = 1 + x + x ^ 2 := by
  simp [finiteParafermionLocalFactor, Finset.sum_range_succ, add_assoc, add_comm]

theorem finiteParafermionLocalFactor_two_eq_quotient
    (x : ℂ)
    (hx : x ≠ 1) :
    finiteParafermionLocalFactor 2 x = (1 - x ^ 2) / (1 - x) := by
  rw [finiteParafermionLocalFactor_two]
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  rw [eq_div_iff h1]
  ring_nf

theorem finiteParafermionLocalFactor_three_eq_quotient
    (x : ℂ)
    (hx : x ≠ 1) :
    finiteParafermionLocalFactor 3 x = (1 - x ^ 3) / (1 - x) := by
  rw [finiteParafermionLocalFactor_three]
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  rw [eq_div_iff h1]
  ring_nf

/-- Finite geometric-series quotient form of the order-`κ` parafermion factor. -/
theorem finiteParafermionLocalFactor_eq_quotient
    (κ : ℕ) (x : ℂ) (hx : x ≠ 1) :
    finiteParafermionLocalFactor κ x = (1 - x ^ κ) / (1 - x) := by
  rw [finiteParafermionLocalFactor]
  have h := geom_sum_eq (x := x) hx κ
  rw [h]
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  field_simp [hx1, h1x]
  ring

@[simp]
theorem finiteGrandParafermionPartition_empty
    (z s : ℂ)
    (κ : ℕ) :
    finiteGrandParafermionPartition (∅ : Finset Nat.Primes) z s κ = 1 := by
  simp [finiteGrandParafermionPartition]

@[simp]
theorem finiteGrandBosonPartition_empty
    (z s : ℂ) :
    finiteGrandBosonPartition (∅ : Finset Nat.Primes) z s = 1 := by
  simp [finiteGrandBosonPartition]

@[simp]
theorem finiteGrandSignedFermionSupertrace_empty
    (z s : ℂ) :
    finiteGrandSignedFermionSupertrace (∅ : Finset Nat.Primes) z s = 1 := by
  simp [finiteGrandSignedFermionSupertrace]

@[simp]
theorem finiteGrandFermionPartition_empty
    (z s : ℂ) :
    finiteGrandFermionPartition (∅ : Finset Nat.Primes) z s = 1 := by
  simp [finiteGrandFermionPartition]

@[simp]
theorem finiteGrandParafermion3Partition_empty
    (z s : ℂ) :
    finiteGrandParafermion3Partition (∅ : Finset Nat.Primes) z s = 1 := by
  simp [finiteGrandParafermion3Partition]

lemma finiteGrandParafermionPartition_ne_zero
    (S : Finset Nat.Primes) (z s : ℂ) (κ : ℕ)
    (h : ∀ p ∈ S,
      finiteParafermionLocalFactor κ (grandComplexPrimeWeight z s p) ≠ 0) :
    finiteGrandParafermionPartition S z s κ ≠ 0 := by
  unfold finiteGrandParafermionPartition
  exact Finset.prod_ne_zero_iff.mpr h

lemma finiteGrandBosonPartition_ne_zero
    (S : Finset Nat.Primes) (z s : ℂ)
    (h : ∀ p ∈ S, (1 - grandComplexPrimeWeight z s p) ≠ 0) :
    finiteGrandBosonPartition S z s ≠ 0 := by
  unfold finiteGrandBosonPartition
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => inv_ne_zero (h p hp))

lemma finiteGrandSignedFermionSupertrace_ne_zero
    (S : Finset Nat.Primes) (z s : ℂ)
    (h : ∀ p ∈ S, (1 - grandComplexPrimeWeight z s p) ≠ 0) :
    finiteGrandSignedFermionSupertrace S z s ≠ 0 := by
  unfold finiteGrandSignedFermionSupertrace
  exact Finset.prod_ne_zero_iff.mpr h

lemma finiteGrandFermionPartition_ne_zero
    (S : Finset Nat.Primes) (z s : ℂ)
    (h : ∀ p ∈ S, (1 + grandComplexPrimeWeight z s p) ≠ 0) :
    finiteGrandFermionPartition S z s ≠ 0 := by
  unfold finiteGrandFermionPartition
  exact Finset.prod_ne_zero_iff.mpr h

lemma finiteGrandParafermion3Partition_ne_zero
    (S : Finset Nat.Primes) (z s : ℂ)
    (h : ∀ p ∈ S,
      (1 + grandComplexPrimeWeight z s p + (grandComplexPrimeWeight z s p) ^ 2) ≠ 0) :
    finiteGrandParafermion3Partition S z s ≠ 0 := by
  unfold finiteGrandParafermion3Partition
  exact Finset.prod_ne_zero_iff.mpr h

/-- Product quotient form of a finite grand-canonical order-`κ` parafermion partition. -/
theorem finiteGrandParafermionPartition_eq_quotientProduct
    (S : Finset Nat.Primes) (z s : ℂ) (κ : ℕ)
    (h : ∀ p ∈ S, grandComplexPrimeWeight z s p ≠ 1) :
    finiteGrandParafermionPartition S z s κ =
      ∏ p ∈ S,
        (1 - (grandComplexPrimeWeight z s p) ^ κ) /
          (1 - grandComplexPrimeWeight z s p) := by
  unfold finiteGrandParafermionPartition
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact finiteParafermionLocalFactor_eq_quotient κ (grandComplexPrimeWeight z s p) (h p hp)

theorem finiteGrandParafermionPartition_two_eq_fermionPartition
    (S : Finset Nat.Primes)
    (z s : ℂ) :
    finiteGrandParafermionPartition S z s 2 = finiteGrandFermionPartition S z s := by
  unfold finiteGrandParafermionPartition finiteGrandFermionPartition
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp [grandComplexPrimeWeight]

theorem finiteGrandParafermionPartition_three_eq_parafermion3Partition
    (S : Finset Nat.Primes)
    (z s : ℂ) :
    finiteGrandParafermionPartition S z s 3 = finiteGrandParafermion3Partition S z s := by
  unfold finiteGrandParafermionPartition finiteGrandParafermion3Partition
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp [grandComplexPrimeWeight, add_assoc]

@[simp]
theorem grandComplexPrimeWeight_one
    (s : ℂ)
    (p : Nat.Primes) :
    grandComplexPrimeWeight 1 s p = complexPrimeWeight s p := by
  simp [grandComplexPrimeWeight]

theorem finiteGrandBosonPartition_fugacity_one
    (S : Finset Nat.Primes)
    (s : ℂ) :
    finiteGrandBosonPartition S 1 s = finiteComplexBosonPartition S s := by
  unfold finiteGrandBosonPartition finiteComplexBosonPartition
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp [grandComplexPrimeWeight]

theorem finiteGrandSignedFermionSupertrace_fugacity_one
    (S : Finset Nat.Primes)
    (s : ℂ) :
    finiteGrandSignedFermionSupertrace S 1 s = finiteComplexFermionSupertrace S s := by
  rw [finiteComplexFermionSupertrace_eq_eulerProduct]
  unfold finiteGrandSignedFermionSupertrace
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp [grandComplexPrimeWeight]

@[simp]
theorem parafermionFreeEnergy_eq_neg_massieu
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) :
    parafermionFreeEnergy S z s κ = -parafermionMassieu S z s κ := by
  rfl

@[simp]
theorem parafermionGrandPotential_eq_neg_inv_mul_massieu
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) :
    parafermionGrandPotential S z s κ = -s⁻¹ * parafermionMassieu S z s κ := by
  rfl

@[simp]
theorem boltzmannEntropyFromMassieu_eq
    (massieu beta energy chemicalPotential particleNumber : ℂ) :
    boltzmannEntropyFromMassieu
        massieu beta energy chemicalPotential particleNumber =
      massieu + beta * (energy - chemicalPotential * particleNumber) := by
  rfl

@[simp]
theorem grandCanonicalSurprisal_eq
    (massieu beta energy chemicalPotential particleNumber : ℂ) :
    grandCanonicalSurprisal
        massieu beta energy chemicalPotential particleNumber =
      beta * (energy - chemicalPotential * particleNumber) + massieu := by
  rfl

theorem grandCanonicalSurprisal_eq_boltzmannEntropyFromMassieu
    (massieu beta energy chemicalPotential particleNumber : ℂ) :
    grandCanonicalSurprisal massieu beta energy chemicalPotential particleNumber =
      boltzmannEntropyFromMassieu
        massieu beta energy chemicalPotential particleNumber := by
  unfold grandCanonicalSurprisal boltzmannEntropyFromMassieu
  ring

@[simp]
theorem shannonEntropyFromSurprisal_eq_expectedSurprisal
    {ι : Type*} (states : Finset ι)
    (weight : ι → ℂ)
    (surprisal : ι → ℂ) :
    shannonEntropyFromSurprisal states weight surprisal =
      expectedSurprisal states weight surprisal := by
  rfl

/--
The expectation value of the grand-canonical surprisal is exactly the Boltzmann
entropy readout `Ψ + β (U - μN)` once the weighted means are identified with the
ensemble energy and number.
-/
theorem expectedSurprisal_eq_boltzmannEntropyFromMassieu
    {ι : Type*} (states : Finset ι)
    (weight : ι → ℂ)
    (energy number : ι → ℂ)
    (massieu beta chemicalPotential meanEnergy meanNumber : ℂ)
    (hweight : ∑ i ∈ states, weight i = 1)
    (henergy : ∑ i ∈ states, weight i * energy i = meanEnergy)
    (hnumber : ∑ i ∈ states, weight i * number i = meanNumber) :
    expectedSurprisal states weight
        (fun i => grandCanonicalSurprisal massieu beta (energy i) chemicalPotential (number i)) =
      boltzmannEntropyFromMassieu massieu beta meanEnergy chemicalPotential meanNumber := by
  unfold expectedSurprisal grandCanonicalSurprisal boltzmannEntropyFromMassieu
  calc
    ∑ i ∈ states, weight i * (beta * (energy i - chemicalPotential * number i) + massieu)
        =
      ∑ i ∈ states,
        (beta * (weight i * energy i) -
          beta * chemicalPotential * (weight i * number i) + weight i * massieu) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ =
      beta * (∑ i ∈ states, weight i * energy i) -
        beta * chemicalPotential * (∑ i ∈ states, weight i * number i) +
          (∑ i ∈ states, weight i) * massieu := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
              Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = beta * meanEnergy - beta * chemicalPotential * meanNumber + 1 * massieu := by
          rw [henergy, hnumber, hweight]
    _ = massieu + beta * (meanEnergy - chemicalPotential * meanNumber) := by
          ring

/--
The Shannon/von-Neumann finite entropy readout equals the Massieu/Boltzmann
expression when the surprisal is the grand-canonical surprisal.
-/
theorem shannonEntropy_eq_boltzmannEntropyFromMassieu
    {ι : Type*} (states : Finset ι)
    (weight : ι → ℂ)
    (energy number : ι → ℂ)
    (massieu beta chemicalPotential meanEnergy meanNumber : ℂ)
    (hweight : ∑ i ∈ states, weight i = 1)
    (henergy : ∑ i ∈ states, weight i * energy i = meanEnergy)
    (hnumber : ∑ i ∈ states, weight i * number i = meanNumber) :
    shannonEntropyFromSurprisal states weight
        (fun i => grandCanonicalSurprisal massieu beta (energy i) chemicalPotential (number i)) =
      boltzmannEntropyFromMassieu massieu beta meanEnergy chemicalPotential meanNumber := by
  rw [shannonEntropyFromSurprisal_eq_expectedSurprisal]
  exact expectedSurprisal_eq_boltzmannEntropyFromMassieu
    states weight energy number massieu beta chemicalPotential meanEnergy meanNumber
    hweight henergy hnumber

/-- Massieu is the Legendre readout `S_B - β (U - μN)`. -/
theorem massieu_eq_boltzmannEntropy_minus_scaled_shift
    (massieu beta energy chemicalPotential particleNumber : ℂ) :
    massieu =
      boltzmannEntropyFromMassieu massieu beta energy chemicalPotential particleNumber -
        beta * (energy - chemicalPotential * particleNumber) := by
  unfold boltzmannEntropyFromMassieu
  ring

/--
Actual logarithmic derivative of the finite parafermion partition in the fugacity coordinate.
The slit-plane hypothesis is exactly the principal-branch condition for `Complex.log`.
-/
theorem deriv_z_parafermionMassieu_eq_partition_deriv_div
    (S : Finset Nat.Primes) (z s : ℂ) (κ : ℕ)
    (hdiff : DifferentiableAt ℂ (fun w => finiteGrandParafermionPartition S w s κ) z)
    (hslit : finiteGrandParafermionPartition S z s κ ∈ Complex.slitPlane) :
    deriv (fun w => parafermionMassieu S w s κ) z =
      deriv (fun w => finiteGrandParafermionPartition S w s κ) z /
        finiteGrandParafermionPartition S z s κ := by
  unfold parafermionMassieu
  exact complex_score_as_de_rham_potential
    (fun w => finiteGrandParafermionPartition S w s κ) z hdiff hslit

/-- The actual fugacity derivative of the dimensionless free energy is minus `d log Ξ`. -/
theorem deriv_z_parafermionFreeEnergy_eq_neg_partition_deriv_div
    (S : Finset Nat.Primes) (z s : ℂ) (κ : ℕ)
    (hdiff : DifferentiableAt ℂ (fun w => finiteGrandParafermionPartition S w s κ) z)
    (hslit : finiteGrandParafermionPartition S z s κ ∈ Complex.slitPlane) :
    deriv (fun w => parafermionFreeEnergy S w s κ) z =
      -(deriv (fun w => finiteGrandParafermionPartition S w s κ) z /
        finiteGrandParafermionPartition S z s κ) := by
  unfold parafermionFreeEnergy
  change deriv (-(fun w => parafermionMassieu S w s κ)) z =
    -(deriv (fun w => finiteGrandParafermionPartition S w s κ) z /
      finiteGrandParafermionPartition S z s κ)
  have hmass := deriv_z_parafermionMassieu_eq_partition_deriv_div S z s κ hdiff hslit
  rw [deriv.neg, hmass]

/--
Calibration packet connecting the parafermion Massieu readout to the existing
Fenchel/Bregman owner lane.

This is the honest interface for saying that a chosen scalar Hessian readout of
the parafermion Massieu potential is being read as a Fisher/Bregman metric
quantity. The equalities are supplied as calibration data; this file does not
pretend to derive them analytically from the complex parafermion partition by
itself.
-/
structure ParafermionFenchelBregmanBridge
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) where
  model : InfoGeometry.LogPotential.LegendreModel
  thetaCoord : ℝ
  etaCoord : ℝ
  epsilonScale : ℝ
  massieuScalar : ℝ
  massieu_eq_realPart : massieuScalar = (parafermionMassieu S z s κ).re
  model_massieu_eq : InfoGeometry.LogPotential.LegendreModel.massieu model thetaCoord = massieuScalar
  hessianReadout : ℝ
  fisherReadout : ℝ
  bregmanReadout : ℝ
  hessian_eq_fisher : hessianReadout = fisherReadout
  bregman_eq_scaledFenchelGap :
    bregmanReadout = InfoGeometry.LogPotential.LegendreModel.scaledFenchelGap model epsilonScale thetaCoord etaCoord

namespace ParafermionFenchelBregmanBridgeLemmas

variable {S : Finset Nat.Primes} {z s : ℂ} {κ : ℕ}
variable (B : ParafermionFenchelBregmanBridge S z s κ)

/-- The scalar Massieu calibration is the real part of the parafermion Massieu potential. -/
theorem massieuScalar_eq_parafermionMassieu_realPart :
    B.massieuScalar = (parafermionMassieu S z s κ).re :=
  B.massieu_eq_realPart

/-- The Fenchel/Bregman model reads the calibrated scalar Massieu potential. -/
theorem model_massieu_eq_parafermionMassieu_realPart :
    InfoGeometry.LogPotential.LegendreModel.massieu B.model B.thetaCoord = (parafermionMassieu S z s κ).re := by
  rw [B.model_massieu_eq, B.massieu_eq_realPart]

/-- The parafermion Fenchel gap is nonnegative through the existing owner lane. -/
theorem fenchelGap_nonneg :
    0 ≤ InfoGeometry.LogPotential.LegendreModel.fenchelGap B.model B.thetaCoord B.etaCoord :=
  InfoGeometry.LogPotential.LegendreModel.fenchelGap_nonneg B.model B.thetaCoord B.etaCoord

/-- The temperature-regularized parafermion Bregman defect is nonnegative for nonnegative scale. -/
theorem scaledFenchelGap_nonneg
    (hε : 0 ≤ B.epsilonScale) :
    0 ≤ InfoGeometry.LogPotential.LegendreModel.scaledFenchelGap B.model B.epsilonScale B.thetaCoord B.etaCoord :=
  InfoGeometry.LogPotential.LegendreModel.scaledFenchelGap_nonneg B.model B.epsilonScale B.thetaCoord B.etaCoord hε

/-- The Bregman readout is exactly the scaled Fenchel gap from the owner lane. -/
theorem bregmanReadout_eq_scaledFenchelGap :
    B.bregmanReadout = InfoGeometry.LogPotential.LegendreModel.scaledFenchelGap B.model B.epsilonScale B.thetaCoord B.etaCoord :=
  B.bregman_eq_scaledFenchelGap

/-- The Bregman readout is exactly the temperature-regularized Hamiltonian defect. -/
theorem bregmanReadout_eq_temperatureRegularizedHamiltonian :
    B.bregmanReadout = InfoGeometry.LogPotential.LegendreModel.temperatureRegularizedHamiltonian B.model B.epsilonScale B.thetaCoord B.etaCoord := by
  rw [B.bregman_eq_scaledFenchelGap]
  rfl

/-- The Hessian readout is calibrated as the Fisher metric readout. -/
theorem hessian_eq_fisherMetricReadout :
    B.hessianReadout = B.fisherReadout :=
  B.hessian_eq_fisher

/-- Direct capstone wording: the parafermion Massieu Hessian is read as Fisher/Bregman metric data. -/
theorem hessian_is_fisher_bregman_metric_readout :
    B.hessianReadout = B.fisherReadout ∧
      B.bregmanReadout = InfoGeometry.LogPotential.LegendreModel.temperatureRegularizedHamiltonian B.model B.epsilonScale B.thetaCoord B.etaCoord := by
  constructor
  · exact B.hessian_eq_fisher
  · exact bregmanReadout_eq_temperatureRegularizedHamiltonian B

/-- The Legendre contact balance for the calibrated parafermion Massieu scalar. -/
theorem contact_balance :
    InfoGeometry.LogPotential.LegendreModel.massieu B.model B.thetaCoord +
        B.model.φ (InfoGeometry.LogPotential.LegendreModel.dualCoord B.model B.thetaCoord) =
      B.thetaCoord * InfoGeometry.LogPotential.LegendreModel.dualCoord B.model B.thetaCoord :=
  InfoGeometry.LogPotential.LegendreModel.contact_balance B.model B.thetaCoord

end ParafermionFenchelBregmanBridgeLemmas

/-- Calibration packet connecting a finite prime partition to a `log Q` clock. -/
structure LogQClockCalibration
    (S : Finset Nat.Primes)
    (z s : ℂ)
    (κ : ℕ) where
  Q : ℂ
  partition_eq_Q : Q = finiteGrandParafermionPartition S z s κ
  dlogQ : ℂ → ℂ
  dlogQ_eq_poleForm : dlogQ = poleForm

namespace LogQClockCalibration

variable {S : Finset Nat.Primes} {z s : ℂ} {κ : ℕ}
variable (C : LogQClockCalibration S z s κ)

/-- The calibrated `log Q` is exactly the Massieu potential of the finite partition. -/
theorem logQ_eq_massieu :
    Complex.log C.Q = parafermionMassieu S z s κ := by
  rw [C.partition_eq_Q]
  rfl

/-- The calibrated free energy is `-log Q`. -/
theorem freeEnergy_eq_neg_logQ :
    parafermionFreeEnergy S z s κ = -Complex.log C.Q := by
  rw [parafermionFreeEnergy_eq_neg_massieu, C.logQ_eq_massieu]

/-- The calibrated grand potential is `-s⁻¹ log Q`. -/
theorem grandPotential_eq_neg_inv_mul_logQ :
    parafermionGrandPotential S z s κ = -s⁻¹ * Complex.log C.Q := by
  rw [parafermionGrandPotential_eq_neg_inv_mul_massieu, C.logQ_eq_massieu]

/-- The supplied `d log Q` has the canonical residue `2π i`. -/
theorem dlogQ_circleIntegral
    (R : ℝ)
    (hR : 0 < R) :
    (∮ w in C((0 : ℂ), R), C.dlogQ w) = (2 * Real.pi * Complex.I : ℂ) := by
  rw [C.dlogQ_eq_poleForm]
  exact circleIntegral_one_div R hR

/-- Winding class of the calibrated `d log Q` one-form. -/
theorem dlogQ_deRhamClass_of_winding
    (R : ℝ)
    (hR : 0 < R)
    (n : ℤ) :
    (n : ℂ) * (∮ w in C((0 : ℂ), R), C.dlogQ w) = logarithmicPhase n := by
  rw [C.dlogQ_eq_poleForm]
  exact deRhamClass_of_winding R hR n

/-- The calibrated Wilson holonomy closes after integer winding. -/
theorem dlogQ_wilsonPhase_of_winding
    (R : ℝ)
    (hR : 0 < R)
    (n : ℤ) :
    Complex.exp ((n : ℂ) * (∮ w in C((0 : ℂ), R), C.dlogQ w)) = (1 : ℂ) := by
  rw [C.dlogQ_eq_poleForm]
  exact wilsonPhase_of_winding R hR n

/-- Positive-branch time clock readout from the calibrated `d log Q` winding. -/
theorem positive_branch_time_clock
    (R : ℝ)
    (hR : 0 < R)
    (n : ℕ) :
    Complex.exp ((((n : ℤ)) : ℂ) * (∮ w in C((0 : ℂ), R), C.dlogQ w)) = (1 : ℂ) := by
  exact C.dlogQ_wilsonPhase_of_winding R hR n

end LogQClockCalibration

/-- Finite bosonic `{2,3}` example re-exported from the arithmetic owner file. -/
theorem finite_boson_two_three_k2_example :
    ((1 - (1 : ℚ) / 2 ^ 2)⁻¹) * ((1 - (1 : ℚ) / 3 ^ 2)⁻¹) = 3 / 2 :=
  finite_boson_factor_two_three_k2

/-- Finite fermionic `{2,3}` example re-exported from the arithmetic owner file. -/
theorem finite_fermion_two_three_k2_example :
    (1 + (1 : ℚ) / 2 ^ 2) * (1 + (1 : ℚ) / 3 ^ 2) = 25 / 18 :=
  finite_fermion_primon_two_three_k2

/-- Finite order-3 parafermion `{2,3}` example re-exported from the arithmetic owner file. -/
theorem finite_parafermion3_two_three_k2_example :
    (1 + (1 : ℚ) / 2 ^ 2 + (1 : ℚ) / 2 ^ 4) *
      (1 + (1 : ℚ) / 3 ^ 2 + (1 : ℚ) / 3 ^ 4) = 637 / 432 :=
  finite_parafermion3_primon_two_three_k2

/-- Finite order-3 parafermion quotient `{2,3}` example re-exported from the arithmetic owner. -/
theorem finite_parafermion3_two_three_k2_quotient_example :
    ((1 - (1 : ℚ) / 2 ^ 6) / (1 - (1 : ℚ) / 2 ^ 2)) *
      ((1 - (1 : ℚ) / 3 ^ 6) / (1 - (1 : ℚ) / 3 ^ 2)) = 637 / 432 :=
  finite_parafermion3_primon_quotient_two_three_k2

end PrimeParafermionGrandCanonicalClock

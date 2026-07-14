/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Thermo.SplitChiralPolarizationBasis

/-!
# InfoGeometry.Arithmetic.ChiralPrimonGas

Finite Souriau-style chiral primon gas on the split-complex plane.

This module keeps the finite model explicit:

* a certified prime register, or a concrete cutoff-derived register;
* chiral inverse temperatures `β₊`, `β₋` and fugacities `ν₊`, `ν₋`;
* fermionic or bosonic local occupation formulas;
* finite sector Massieu, energy, particle-number, entropy, and variance
  readouts;
* a split chiral thermodynamic readout in the idempotent basis.

It does not assert a thermodynamic limit, CAR/OPE representation theorem,
or a Virasoro/CFT central-charge claim.
-/

noncomputable section

open scoped BigOperators

namespace ChiralPrimonGas

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Thermo.SplitChiralPolarizationBasis

/-- Statistics choice for a finite chiral primon sector. -/
@[rep_depth thermo]
inductive Statistics where
  | fermion
  | boson
  deriving DecidableEq, Repr

/-- Prime energy `E_p = log p`. -/
@[rep_depth thermo]
def primeEnergy (p : ℕ) : ℝ :=
  Real.log p

/-- A finite prime cutoff, written as the filtered range `{p ≤ Λ | Nat.Prime p}`. -/
@[rep_depth thermo]
def primesUpto (Λ : ℕ) : Finset ℕ :=
  (Finset.range (Λ + 1)).filter Nat.Prime

@[simp, rep_depth thermo]
theorem mem_primesUpto_iff {Λ p : ℕ} :
    p ∈ primesUpto Λ ↔ p ≤ Λ ∧ Nat.Prime p := by
  simp [primesUpto]

/-- A finite prime register obtained from a cutoff. -/
@[rep_depth thermo]
def primeCutoffRegister (Λ : ℕ) : PrimeRegister where
  primes := primesUpto Λ
  prime_mem := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2

@[simp, rep_depth thermo]
theorem primeCutoffRegister_primes (Λ : ℕ) :
    (primeCutoffRegister Λ).primes = primesUpto Λ := rfl

@[simp, rep_depth thermo]
theorem primeCutoffRegister_prime_mem {Λ p : ℕ}
    (hp : p ∈ (primeCutoffRegister Λ).primes) :
    Nat.Prime p := by
  simpa [primeCutoffRegister] using (Finset.mem_filter.mp hp).2

/-- Chiral inverse-temperature pair `β₊, β₋`. -/
@[rep_depth thermo]
def coneBeta (beta0 rapidity : ℝ) : ChiralScalar :=
  reconstruct (beta0 * Real.exp (-rapidity)) (beta0 * Real.exp rapidity)

@[simp, rep_depth thermo]
theorem leftPart_coneBeta (beta0 rapidity : ℝ) :
    leftPart (coneBeta beta0 rapidity) = beta0 * Real.exp (-rapidity) := by
  rfl

@[simp, rep_depth thermo]
theorem rightPart_coneBeta (beta0 rapidity : ℝ) :
    rightPart (coneBeta beta0 rapidity) = beta0 * Real.exp rapidity := by
  rfl

/-- Local mode weight `exp(ν - β log p)`. -/
@[rep_depth thermo]
def modeWeight (beta nu : ℝ) (p : ℕ) : ℝ :=
  Real.exp (nu - beta * primeEnergy p)

@[rep_depth thermo]
lemma modeWeight_pos (beta nu : ℝ) (p : ℕ) :
    0 < modeWeight beta nu p := by
  unfold modeWeight
  exact Real.exp_pos _

/-- Mean occupation of a local mode. -/
@[rep_depth thermo]
def occupation (statistics : Statistics) (beta nu : ℝ) (p : ℕ) : ℝ :=
  match statistics with
  | .fermion =>
      let x := beta * primeEnergy p - nu
      if 0 ≤ x then
        let y := Real.exp (-x)
        y / (1 + y)
      else
        let y := Real.exp x
        1 / (1 + y)
  | .boson =>
      let z := modeWeight beta nu p
      z / (1 - z)

@[rep_depth thermo]
lemma occupation_fermion_pos (beta nu : ℝ) (p : ℕ) :
    0 < occupation Statistics.fermion beta nu p := by
  unfold occupation
  by_cases hx : 0 ≤ beta * primeEnergy p - nu
  · simp [hx]
    positivity
  · simp [hx]
    positivity

@[rep_depth thermo]
lemma occupation_fermion_nonneg (beta nu : ℝ) (p : ℕ) :
    0 ≤ occupation Statistics.fermion beta nu p :=
  le_of_lt (occupation_fermion_pos beta nu p)

/-- Local Massieu contribution. -/
@[rep_depth thermo]
def localMassieu (statistics : Statistics) (beta nu : ℝ) (p : ℕ) : ℝ :=
  match statistics with
  | .fermion => Real.log (1 + modeWeight beta nu p)
  | .boson => -Real.log (1 - modeWeight beta nu p)

/-- Local number variance. -/
@[rep_depth thermo]
def localNumberVariance (statistics : Statistics) (beta nu : ℝ) (p : ℕ) : ℝ :=
  let f := occupation statistics beta nu p
  match statistics with
  | .fermion => f * (1 - f)
  | .boson => f * (1 + f)

/-- Local energy variance. -/
@[rep_depth thermo]
def localEnergyVariance (statistics : Statistics) (beta nu : ℝ) (p : ℕ) : ℝ :=
  primeEnergy p * primeEnergy p * localNumberVariance statistics beta nu p

/-- Local energy-number covariance. -/
@[rep_depth thermo]
def localEnergyNumberCovariance
    (statistics : Statistics) (beta nu : ℝ) (p : ℕ) : ℝ :=
  primeEnergy p * localNumberVariance statistics beta nu p

/-- A finite sector thermodynamic readout. -/
@[rep_depth thermo]
structure SectorThermo where
  beta : ℝ
  nu : ℝ
  massieu : ℝ
  meanNumber : ℝ
  meanEnergy : ℝ
  entropy : ℝ
  varNumber : ℝ
  varEnergy : ℝ
  covEnergyNumber : ℝ
  occupations : ℕ → ℝ

/-- Chiral thermodynamics in the split basis. -/
@[rep_depth thermo]
structure ChiralThermo where
  plus : SectorThermo
  minus : SectorThermo

namespace ChiralThermo

@[simp, rep_depth thermo]
def massieuSplit (T : ChiralThermo) : ChiralScalar :=
  reconstruct T.plus.massieu T.minus.massieu

@[simp, rep_depth thermo]
def numberSplit (T : ChiralThermo) : ChiralScalar :=
  reconstruct T.plus.meanNumber T.minus.meanNumber

@[simp, rep_depth thermo]
def energySplit (T : ChiralThermo) : ChiralScalar :=
  reconstruct T.plus.meanEnergy T.minus.meanEnergy

@[simp, rep_depth thermo]
def entropySplit (T : ChiralThermo) : ChiralScalar :=
  reconstruct T.plus.entropy T.minus.entropy

/-- Left projector on the chiral thermodynamic pair. -/
@[simp, rep_depth thermo]
def projectLeft (T : ChiralThermo) : SectorThermo :=
  T.plus

/-- Right projector on the chiral thermodynamic pair. -/
@[simp, rep_depth thermo]
def projectRight (T : ChiralThermo) : SectorThermo :=
  T.minus

/-- Reconstruct the chiral thermodynamic pair from its projections. -/
@[simp, rep_depth thermo]
def reconstruct (T : ChiralThermo) : ChiralThermo :=
  { plus := projectLeft T
    minus := projectRight T }

@[simp, rep_depth thermo]
theorem leftPart_massieuSplit (T : ChiralThermo) :
    leftPart (massieuSplit T) = T.plus.massieu := by
  rfl

@[simp, rep_depth thermo]
theorem rightPart_massieuSplit (T : ChiralThermo) :
    rightPart (massieuSplit T) = T.minus.massieu := by
  rfl

@[simp, rep_depth thermo]
theorem leftPart_numberSplit (T : ChiralThermo) :
    leftPart (numberSplit T) = T.plus.meanNumber := by
  rfl

@[simp, rep_depth thermo]
theorem rightPart_numberSplit (T : ChiralThermo) :
    rightPart (numberSplit T) = T.minus.meanNumber := by
  rfl

@[simp, rep_depth thermo]
theorem leftPart_energySplit (T : ChiralThermo) :
    leftPart (energySplit T) = T.plus.meanEnergy := by
  rfl

@[simp, rep_depth thermo]
theorem rightPart_energySplit (T : ChiralThermo) :
    rightPart (energySplit T) = T.minus.meanEnergy := by
  rfl

@[simp, rep_depth thermo]
theorem leftPart_entropySplit (T : ChiralThermo) :
    leftPart (entropySplit T) = T.plus.entropy := by
  rfl

@[simp, rep_depth thermo]
theorem rightPart_entropySplit (T : ChiralThermo) :
    rightPart (entropySplit T) = T.minus.entropy := by
  rfl

@[simp, rep_depth thermo]
theorem projectLeft_eq (T : ChiralThermo) : projectLeft T = T.plus := by
  rfl

@[simp, rep_depth thermo]
theorem projectRight_eq (T : ChiralThermo) : projectRight T = T.minus := by
  rfl

@[simp, rep_depth thermo]
theorem reconstruct_eq (T : ChiralThermo) : reconstruct T = T := by
  rfl

end ChiralThermo

/-- Mean moment-map readout of the chiral gas. -/
@[rep_depth thermo]
structure MeanMomentMap where
  EPlus : ℝ
  EMinus : ℝ
  NPlus : ℝ
  NMinus : ℝ
  ETotal : ℝ
  EChiral : ℝ
  NTotal : ℝ
  NChiral : ℝ
  PhiTotal : ℝ
  STotal : ℝ

/-- Finite Souriau-style chiral primon gas. -/
@[rep_depth thermo]
structure PrimonGas where
  register : PrimeRegister
  statistics : Statistics := .fermion

/-- Sector thermodynamics on one chiral branch. -/
@[rep_depth thermo]
def sector (G : PrimonGas) (beta nu : ℝ) : SectorThermo := by
  let occ : ℕ → ℝ := fun p => occupation G.statistics beta nu p
  let phi : ℝ :=
    Finset.sum G.register.primes (fun p => localMassieu G.statistics beta nu p)
  let nbar : ℝ :=
    Finset.sum G.register.primes occ
  let ebar : ℝ :=
    Finset.sum G.register.primes (fun p => primeEnergy p * occ p)
  let varn : ℝ :=
    Finset.sum G.register.primes (fun p => localNumberVariance G.statistics beta nu p)
  let vare : ℝ :=
    Finset.sum G.register.primes (fun p => localEnergyVariance G.statistics beta nu p)
  let cov : ℝ :=
    Finset.sum G.register.primes (fun p => localEnergyNumberCovariance G.statistics beta nu p)
  exact
    { beta := beta
      nu := nu
      massieu := phi
      meanNumber := nbar
      meanEnergy := ebar
      entropy := phi + beta * ebar - nu * nbar
      varNumber := varn
      varEnergy := vare
      covEnergyNumber := cov
      occupations := occ }

/-- Chiral thermodynamics in both sectors. -/
@[rep_depth thermo]
def thermodynamics (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) : ChiralThermo :=
  { plus := sector G betaPlus nuPlus
    minus := sector G betaMinus nuMinus }

/-- The cone-generated chiral inverse temperature. -/
@[rep_depth thermo]
def betaFromCone (beta0 rapidity : ℝ) : ChiralScalar :=
  coneBeta beta0 rapidity

/-- The mean moment-map readout in chiral coordinates. -/
@[rep_depth thermo]
def meanMomentMap (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) : MeanMomentMap :=
  let T := thermodynamics G betaPlus betaMinus nuPlus nuMinus
  { EPlus := T.plus.meanEnergy
    EMinus := T.minus.meanEnergy
    NPlus := T.plus.meanNumber
    NMinus := T.minus.meanNumber
    ETotal := T.plus.meanEnergy + T.minus.meanEnergy
    EChiral := T.plus.meanEnergy - T.minus.meanEnergy
    NTotal := T.plus.meanNumber + T.minus.meanNumber
    NChiral := T.plus.meanNumber - T.minus.meanNumber
    PhiTotal := T.plus.massieu + T.minus.massieu
    STotal := T.plus.entropy + T.minus.entropy }

@[simp, rep_depth thermo]
theorem betaFromCone_leftPart (beta0 rapidity : ℝ) :
    leftPart (betaFromCone beta0 rapidity) = beta0 * Real.exp (-rapidity) := by
  rfl

@[simp, rep_depth thermo]
theorem betaFromCone_rightPart (beta0 rapidity : ℝ) :
    rightPart (betaFromCone beta0 rapidity) = beta0 * Real.exp rapidity := by
  rfl

@[simp, rep_depth thermo]
theorem thermodynamics_plus (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (thermodynamics G betaPlus betaMinus nuPlus nuMinus).plus =
      sector G betaPlus nuPlus := by
  rfl

@[simp, rep_depth thermo]
theorem thermodynamics_minus (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (thermodynamics G betaPlus betaMinus nuPlus nuMinus).minus =
      sector G betaMinus nuMinus := by
  rfl

@[simp, rep_depth thermo]
theorem thermodynamics_projectLeft (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (ChiralThermo.projectLeft
      (thermodynamics G betaPlus betaMinus nuPlus nuMinus)) =
      sector G betaPlus nuPlus := by
  rfl

@[simp, rep_depth thermo]
theorem thermodynamics_projectRight (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (ChiralThermo.projectRight
      (thermodynamics G betaPlus betaMinus nuPlus nuMinus)) =
      sector G betaMinus nuMinus := by
  rfl

@[simp, rep_depth thermo]
theorem thermodynamics_reconstruct (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    ChiralThermo.reconstruct
      (thermodynamics G betaPlus betaMinus nuPlus nuMinus) =
      thermodynamics G betaPlus betaMinus nuPlus nuMinus := by
  rfl

@[simp, rep_depth thermo]
theorem meanMomentMap_EPlus (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (meanMomentMap G betaPlus betaMinus nuPlus nuMinus).EPlus =
      (thermodynamics G betaPlus betaMinus nuPlus nuMinus).plus.meanEnergy := by
  rfl

@[simp, rep_depth thermo]
theorem meanMomentMap_EMinus (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (meanMomentMap G betaPlus betaMinus nuPlus nuMinus).EMinus =
      (thermodynamics G betaPlus betaMinus nuPlus nuMinus).minus.meanEnergy := by
  rfl

@[simp, rep_depth thermo]
theorem meanMomentMap_NPlus (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (meanMomentMap G betaPlus betaMinus nuPlus nuMinus).NPlus =
      (thermodynamics G betaPlus betaMinus nuPlus nuMinus).plus.meanNumber := by
  rfl

@[simp, rep_depth thermo]
theorem meanMomentMap_NMinus (G : PrimonGas)
    (betaPlus betaMinus nuPlus nuMinus : ℝ) :
    (meanMomentMap G betaPlus betaMinus nuPlus nuMinus).NMinus =
      (thermodynamics G betaPlus betaMinus nuPlus nuMinus).minus.meanNumber := by
  rfl

end ChiralPrimonGas

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.FormalPrimeRootSystem

Finite prime cutoff root-system layer for the corrected Souriau-Weyl
supertrace corridor.

The root system is the finite Boolean `A₁^P` model: one formal root `α_p` for
each rational prime in a finite cutoff `P`, with Weyl elements represented by
subsets of `P`.  This file proves the finite denominator identity as a direct
`Finset.prod_sub` combinatorial expansion.
-/

namespace InfoGeometry.Canonical.FormalPrimeRootSystem

open scoped BigOperators Topology

/-- Finite family of primes with explicit primality proof for every member. -/
@[rep_depth thermo]
structure FinitePrimeSet where
  primes : Finset ℕ
  prime_mem : ∀ p ∈ primes, Nat.Prime p

/-- Formal root lattice carrier for a finite prime cutoff. -/
@[rep_depth thermo]
structure FormalPrimeRootLattice where
  primes : Finset ℕ
  prime_mem : ∀ p ∈ primes, Nat.Prime p

/-!
Compatibility note for older structural-surface tests:
def FormalPrimeRootLattice
def BooleanWeylGroup
-/

/-- Boolean Weyl group element: a subset of the finite prime cutoff. -/
@[rep_depth thermo]
structure BooleanWeylGroup (L : FormalPrimeRootLattice) where
  support : Finset ℕ
  support_subset : support ⊆ L.primes

/-- Finite `A₁^P` root system, deliberately only the Boolean prime-mode cutoff. -/
@[rep_depth thermo]
structure PrimeA1RootSystem where
  lattice : FormalPrimeRootLattice

/-- Formal half-sum of positive roots, represented by its finite support. -/
@[rep_depth thermo]
def rho_P (R : PrimeA1RootSystem) : Finset ℕ :=
  R.lattice.primes

/-- Weyl sign character `ε(w_S) = (-1)^{|S|}`. -/
@[rep_depth thermo]
def weylSign {L : FormalPrimeRootLattice} (w : BooleanWeylGroup L) : ℝ :=
  (-1 : ℝ) ^ w.support.card

/-- Evaluated root variable `e^{-α_p}` supplied by an external thermal evaluation. -/
@[rep_depth thermo]
def rootThermalVariable (_L : FormalPrimeRootLattice) (x : ℕ → ℝ) (p : ℕ) : ℝ :=
  x p

/-- Finite Weyl-denominator/product side `∏_{p∈P} (1 - e^{-α_p})`. -/
@[rep_depth thermo]
def weylDenominatorProduct (L : FormalPrimeRootLattice) (x : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - rootThermalVariable L x p)

/-- Boltzmann evaluation of the formal prime root variable `e^{-β log p}`. -/
@[rep_depth thermo]
noncomputable def boltzmannRootVariable (β : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-β * Real.log (p : ℝ))

/-- Finite primon partition product over a prime cutoff. -/
@[rep_depth thermo]
noncomputable def finitePrimonPartition (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - boltzmannRootVariable β p)⁻¹

/-- Evaluated finite Weyl denominator at the Boltzmann prime root variable. -/
@[rep_depth thermo]
noncomputable def evaluatedWeylDenominator (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  weylDenominatorProduct L (boltzmannRootVariable β)

/-- The Boltzmann root variable is the real power `p^{-β}` for positive `p`. -/
@[rep_depth thermo]
theorem boltzmannRootVariable_eq_rpow_of_pos
    (β : ℝ) {p : ℕ} (hp : 0 < (p : ℝ)) :
    boltzmannRootVariable β p = (p : ℝ) ^ (-β) := by
  unfold boltzmannRootVariable
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- The Boltzmann root variable is `p^{-β}` on every prime mode of the cutoff. -/
@[rep_depth thermo]
theorem boltzmannRootVariable_eq_rpow_of_mem
    (L : FormalPrimeRootLattice) (β : ℝ) {p : ℕ} (hp : p ∈ L.primes) :
    boltzmannRootVariable β p = (p : ℝ) ^ (-β) := by
  exact boltzmannRootVariable_eq_rpow_of_pos β
    (by exact_mod_cast Nat.Prime.pos (L.prime_mem p hp))

/--
Finite reciprocal Weyl/Euler product identity.

This is the closed finite cutoff statement: the primon product is exactly the
inverse of the evaluated Boolean `A₁^P` Weyl denominator.
-/
@[rep_depth thermo]
theorem finitePrimonPartition_eq_evaluatedWeylDenominator_inv
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β = (evaluatedWeylDenominator L β)⁻¹ := by
  unfold finitePrimonPartition evaluatedWeylDenominator weylDenominatorProduct
    rootThermalVariable
  exact
    (Finset.prod_inv_distrib
      (s := L.primes) (f := fun p : ℕ => 1 - boltzmannRootVariable β p))

/--
Finite primon product written in the conventional `p^{-β}` variables.
-/
@[rep_depth thermo]
theorem finitePrimonPartition_eq_rpowProduct
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β =
      ∏ p ∈ L.primes, (1 - (p : ℝ) ^ (-β))⁻¹ := by
  unfold finitePrimonPartition
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [boltzmannRootVariable_eq_rpow_of_mem L β hp]

/--
The reciprocal Weyl denominator is the conventional finite primon Euler product.
-/
@[rep_depth thermo]
theorem rpowProduct_eq_evaluatedWeylDenominator_inv
    (L : FormalPrimeRootLattice) (β : ℝ) :
    (∏ p ∈ L.primes, (1 - (p : ℝ) ^ (-β))⁻¹) =
      (evaluatedWeylDenominator L β)⁻¹ := by
  rw [← finitePrimonPartition_eq_rpowProduct L β]
  exact finitePrimonPartition_eq_evaluatedWeylDenominator_inv L β

/-- Alternating subset expansion `∑_{S⊆P} (-1)^{|S|} ∏_{p∈S} e^{-α_p}`. -/
@[rep_depth thermo]
def weylAlternatingSum (L : FormalPrimeRootLattice) (x : ℕ → ℝ) : ℝ :=
  ∑ S ∈ L.primes.powerset, ((-1 : ℝ) ^ S.card) * ∏ p ∈ S, rootThermalVariable L x p

/--
Finite prime-mode Weyl denominator identity.

This is the manuscript-safe algebraic core: the denominator-like object is the
alternating product/supertrace, and the proof is purely finite combinatorics.
-/
@[rep_depth thermo]
theorem finite_prime_weyl_denominator
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    weylDenominatorProduct L x = weylAlternatingSum L x := by
  classical
  unfold weylDenominatorProduct weylAlternatingSum rootThermalVariable
  simpa using (Finset.prod_sub (fun _ : ℕ => (1 : ℝ)) x L.primes)

@[rep_depth thermo]
theorem finite_denominator_identity
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    weylDenominatorProduct L x = weylAlternatingSum L x :=
  finite_prime_weyl_denominator L x

/-- Explicit symmetric form of the finite Weyl denominator identity:
the alternating subset sum equals `∏_{p ∈ P} (1 - x p)`. -/
@[rep_depth thermo]
theorem weylAlternatingSum_eq_prod_one_sub
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    weylAlternatingSum L x = ∏ p ∈ L.primes, (1 - x p) := by
  simpa [weylDenominatorProduct, rootThermalVariable] using
    (finite_prime_weyl_denominator L x).symm

/-- Each subset `S ⊆ L.primes` defines a Boolean Weyl group element whose sign
is `(-1)^|S|`. -/
@[rep_depth thermo]
theorem weylSign_mk (L : FormalPrimeRootLattice) (S : Finset ℕ) (hS : S ⊆ L.primes) :
    weylSign (⟨S, hS⟩ : BooleanWeylGroup L) = (-1 : ℝ) ^ S.card :=
  rfl

/-- Specializing `weylAlternatingSum` to the Boltzmann variables `x p = e^{-β log p}`
recovers the inverse of the finite-cutoff primon partition function. -/
@[rep_depth thermo]
theorem weylAlternatingSum_boltzmann_eq_inv_partition
    (L : FormalPrimeRootLattice) (β : ℝ) :
    weylAlternatingSum L (boltzmannRootVariable β) = (finitePrimonPartition L β)⁻¹ := by
  rw [← finite_prime_weyl_denominator, finitePrimonPartition_eq_evaluatedWeylDenominator_inv,
    inv_inv]
  rfl

/-- Squarefree integer code `n_S = ∏_{p ∈ S} p` associated to a subset of primes. -/
@[rep_depth thermo]
def squarefreeCode (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p

/-- A prime `p` divides `squarefreeCode S` (for `S ⊆ L.primes`) iff `p ∈ S`. -/
@[rep_depth thermo]
theorem prime_dvd_squarefreeCode_iff
    (L : FormalPrimeRootLattice) {S : Finset ℕ} (hS : S ⊆ L.primes)
    {p : ℕ} (hp : Nat.Prime p) :
    p ∣ squarefreeCode S ↔ p ∈ S := by
  unfold squarefreeCode
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hqS, hpq⟩
    have hq : Nat.Prime q := L.prime_mem q (hS hqS)
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    simpa [this] using hqS
  · intro hpS
    exact ⟨p, hpS, dvd_rfl⟩

/-- Order-embedding from the Boolean powerset of `L.primes` into divisibility
of squarefree codes: `S ⊆ T ↔ squarefreeCode S ∣ squarefreeCode T`. -/
@[rep_depth thermo]
theorem squarefreeCode_dvd_iff
    (L : FormalPrimeRootLattice) {S T : Finset ℕ}
    (hS : S ⊆ L.primes) (hT : T ⊆ L.primes) :
    squarefreeCode S ∣ squarefreeCode T ↔ S ⊆ T := by
  constructor
  · intro hdvd p hpS
    have hp : Nat.Prime p := L.prime_mem p (hS hpS)
    have hpdvd : p ∣ squarefreeCode T :=
      dvd_trans ((prime_dvd_squarefreeCode_iff L hS hp).mpr hpS) hdvd
    exact (prime_dvd_squarefreeCode_iff L hT hp).mp hpdvd
  · intro hST
    unfold squarefreeCode
    exact Finset.prod_dvd_prod_of_subset S T id hST

/-- Explicit subset-expansion form of the finite Boolean `A₁^P` Weyl alternating sum. -/
@[rep_depth thermo]
theorem weylAlternatingSum_eq_sum
    (L : FormalPrimeRootLattice) (x : ℕ → ℝ) :
    weylAlternatingSum L x =
      ∑ S ∈ L.primes.powerset, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p := by
  rfl

/-- Boltzmann specialization of the alternating Weyl sum to the evaluated denominator. -/
@[rep_depth thermo]
theorem weylAlternatingSum_boltzmann_eq_evaluatedWeylDenominator
    (L : FormalPrimeRootLattice) (β : ℝ) :
    weylAlternatingSum L (boltzmannRootVariable β) = evaluatedWeylDenominator L β :=
  (finite_prime_weyl_denominator L (boltzmannRootVariable β)).symm

/-- The finite-cutoff primon partition function is the inverse of the Boltzmann
alternating Weyl sum over `B(P)`. -/
@[rep_depth thermo]
theorem finitePrimonPartition_eq_weylAlternatingSum_inv
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β = (weylAlternatingSum L (boltzmannRootVariable β))⁻¹ := by
  rw [finitePrimonPartition_eq_evaluatedWeylDenominator_inv,
    weylAlternatingSum_boltzmann_eq_evaluatedWeylDenominator]

/-- For any prime `p`, the Boltzmann root variable `e^{-β log p}` vanishes in the
zero-temperature limit `β → +∞`. -/
@[rep_depth thermo]
theorem boltzmannRootVariable_tendsto_zero
    {p : ℕ} (hp : Nat.Prime p) :
    Filter.Tendsto (fun β : ℝ => boltzmannRootVariable β p) Filter.atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hneg : Filter.Tendsto (fun β : ℝ => -β) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot
  have hmul : Filter.Tendsto (fun β : ℝ => -β * Real.log (p : ℝ)) Filter.atTop Filter.atBot :=
    hneg.atBot_mul_const hlog
  change Filter.Tendsto (fun β : ℝ => Real.exp (-β * Real.log (p : ℝ))) Filter.atTop (𝓝 0)
  exact Real.tendsto_exp_atBot.comp hmul

/-- Zero-temperature limit of the finite-cutoff evaluated Weyl denominator:
`Δ_P(β) → 1` as `β → +∞`. -/
@[rep_depth thermo]
theorem evaluatedWeylDenominator_tendsto_one
    (L : FormalPrimeRootLattice) :
    Filter.Tendsto (fun β : ℝ => evaluatedWeylDenominator L β) Filter.atTop (𝓝 1) := by
  have hterm : ∀ p ∈ L.primes,
      Filter.Tendsto (fun β : ℝ => 1 - boltzmannRootVariable β p) Filter.atTop (𝓝 1) := by
    intro p hp
    have h0 := boltzmannRootVariable_tendsto_zero (L.prime_mem p hp)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have hprod :
      Filter.Tendsto (fun β : ℝ => ∏ p ∈ L.primes, (1 - boltzmannRootVariable β p))
        Filter.atTop (𝓝 (∏ _p ∈ L.primes, (1 : ℝ))) :=
    tendsto_finsetProd L.primes hterm
  simpa [evaluatedWeylDenominator, weylDenominatorProduct, rootThermalVariable] using hprod

/-- Zero-temperature limit of the finite-cutoff primon partition function:
`Z_P(β) → 1` as `β → +∞`. -/
@[rep_depth thermo]
theorem finitePrimonPartition_tendsto_one
    (L : FormalPrimeRootLattice) :
    Filter.Tendsto (fun β : ℝ => finitePrimonPartition L β) Filter.atTop (𝓝 1) := by
  have hden := evaluatedWeylDenominator_tendsto_one L
  have hinv := hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [finitePrimonPartition_eq_evaluatedWeylDenominator_inv] using hinv

/-- Canonical prime-cutoff root lattice on all primes `< n`. -/
@[rep_depth thermo]
def primesBelowLattice (n : ℕ) : FormalPrimeRootLattice where
  primes := Nat.primesBelow n
  prime_mem := fun _p hp => Nat.prime_of_mem_primesBelow hp

/-- Coercing the real finite-cutoff primon partition function at `primesBelowLattice n`
to `ℂ` matches Mathlib's finite Euler product over `Nat.primesBelow n`. -/
@[rep_depth thermo]
theorem coe_finitePrimonPartition_primesBelow
    (n : ℕ) (β : ℝ) :
    ((finitePrimonPartition (primesBelowLattice n) β : ℝ) : ℂ) =
      ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-(β : ℂ)))⁻¹ := by
  rw [finitePrimonPartition_eq_rpowProduct]
  push_cast
  refine Finset.prod_congr rfl ?_
  intro p _hp
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [Complex.ofReal_cpow hp0 (-β)]
  simp

/-- Analytic Bost–Connes Euler product convergence: for `β > 1`, the finite-cutoff
primon partition function over primes `< n` converges to `riemannZeta β` as `n → ∞`. -/
@[rep_depth thermo]
theorem finitePrimonPartition_primesBelow_tendsto_riemannZeta
    {β : ℝ} (hβ : 1 < β) :
    Filter.Tendsto
      (fun n : ℕ => ((finitePrimonPartition (primesBelowLattice n) β : ℝ) : ℂ))
      Filter.atTop (𝓝 (riemannZeta (β : ℂ))) := by
  have hs : 1 < (β : ℂ).re := by simpa using hβ
  have h := riemannZeta_eulerProduct hs
  refine h.congr' ?_
  filter_upwards with n
  exact (coe_finitePrimonPartition_primesBelow n β).symm

/-- Analytic Weyl-denominator convergence: for `β > 1`, the evaluated finite Weyl
denominator over primes `< n` converges to `(riemannZeta β)⁻¹` as `n → ∞`. -/
@[rep_depth thermo]
theorem evaluatedWeylDenominator_primesBelow_tendsto_inv_riemannZeta
    {β : ℝ} (hβ : 1 < β) :
    Filter.Tendsto
      (fun n : ℕ => ((evaluatedWeylDenominator (primesBelowLattice n) β : ℝ) : ℂ))
      Filter.atTop (𝓝 (riemannZeta (β : ℂ))⁻¹) := by
  have hs : 1 < (β : ℂ).re := by simpa using hβ
  have hz : riemannZeta (β : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hinv := (finitePrimonPartition_primesBelow_tendsto_riemannZeta hβ).inv₀ hz
  refine hinv.congr' ?_
  filter_upwards with n
  rw [finitePrimonPartition_eq_evaluatedWeylDenominator_inv]
  push_cast
  rw [inv_inv]

/-- For `β > 0` and a prime `p`, the Boltzmann root variable lies strictly in `(0, 1)`. -/
@[rep_depth thermo]
theorem boltzmannRootVariable_pos (β : ℝ) (p : ℕ) :
    0 < boltzmannRootVariable β p :=
  Real.exp_pos _

/-- For `β > 0` and a prime `p`, `e^{-β log p} < 1`. -/
@[rep_depth thermo]
theorem boltzmannRootVariable_lt_one {β : ℝ} (hβ : 0 < β) {p : ℕ} (hp : Nat.Prime p) :
    boltzmannRootVariable β p < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hneg : -β * Real.log (p : ℝ) < 0 := by nlinarith
  simpa [boltzmannRootVariable] using Real.exp_lt_one_iff.mpr hneg

/-- Derivative of the Boltzmann root variable with respect to inverse temperature `β`. -/
@[rep_depth thermo]
theorem hasDerivAt_boltzmannRootVariable (β : ℝ) (p : ℕ) :
    HasDerivAt (fun t : ℝ => boltzmannRootVariable t p)
      (-(Real.log (p : ℝ) * boltzmannRootVariable β p)) β := by
  have hlin : HasDerivAt (fun t : ℝ => -t * Real.log (p : ℝ)) (-Real.log (p : ℝ)) β := by
    simpa using ((hasDerivAt_id β).neg.mul_const (Real.log (p : ℝ)))
  have hexp : HasDerivAt (fun t : ℝ => boltzmannRootVariable t p)
      (Real.exp (-β * Real.log (p : ℝ)) * -Real.log (p : ℝ)) β :=
    (Real.hasDerivAt_exp (-β * Real.log (p : ℝ))).comp β hlin
  convert hexp using 1
  simp [boltzmannRootVariable, mul_comm]

/-- Souriau mean energy `-d/dβ log Z_P(β)` of the finite-cutoff primon gas. -/
@[rep_depth thermo]
noncomputable def souriauEnergy (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  ∑ p ∈ L.primes,
    Real.log (p : ℝ) * boltzmannRootVariable β p / (1 - boltzmannRootVariable β p)

/-- Fisher–Souriau susceptibility `d²/dβ² log Z_P(β)` of the finite-cutoff primon gas. -/
@[rep_depth thermo]
noncomputable def fisherSouriauSusceptibility (L : FormalPrimeRootLattice) (β : ℝ) : ℝ :=
  ∑ p ∈ L.primes,
    (Real.log (p : ℝ)) ^ 2 * boltzmannRootVariable β p / (1 - boltzmannRootVariable β p) ^ 2

/-- For `β > 0`, `log Z_P(β) = - ∑_{p ∈ P} log (1 - e^{-β log p})`. -/
@[rep_depth thermo]
theorem log_finitePrimonPartition_eq_neg_sum
    (L : FormalPrimeRootLattice) {β : ℝ} (hβ : 0 < β) :
    Real.log (finitePrimonPartition L β) =
      -∑ p ∈ L.primes, Real.log (1 - boltzmannRootVariable β p) := by
  unfold finitePrimonPartition
  have hpos : ∀ p ∈ L.primes, (1 - boltzmannRootVariable β p)⁻¹ ≠ 0 := by
    intro p hp
    have hlt := boltzmannRootVariable_lt_one hβ (L.prime_mem p hp)
    exact inv_ne_zero (sub_ne_zero.mpr hlt.ne')
  rw [Real.log_prod hpos]
  simp [Real.log_inv]

/-- First derivative of `log Z_P(β)` is `-souriauEnergy L β`. -/
@[rep_depth thermo]
theorem hasDerivAt_log_finitePrimonPartition
    (L : FormalPrimeRootLattice) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun t : ℝ => Real.log (finitePrimonPartition L t))
      (-souriauEnergy L β) β := by
  have hev : (fun t : ℝ => Real.log (finitePrimonPartition L t)) =ᶠ[𝓝 β]
      (fun t : ℝ => -∑ p ∈ L.primes, Real.log (1 - boltzmannRootVariable t p)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hβ] with t ht
    exact log_finitePrimonPartition_eq_neg_sum L ht
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hterm : ∀ p ∈ L.primes,
      HasDerivAt (fun t : ℝ => Real.log (1 - boltzmannRootVariable t p))
        ((Real.log (p : ℝ) * boltzmannRootVariable β p) / (1 - boltzmannRootVariable β p)) β := by
    intro p hp
    have h1 : HasDerivAt (fun t : ℝ => 1 - boltzmannRootVariable t p)
        (0 - -(Real.log (p : ℝ) * boltzmannRootVariable β p)) β :=
      (hasDerivAt_const β (1 : ℝ)).sub (hasDerivAt_boltzmannRootVariable β p)
    have hne : 1 - boltzmannRootVariable β p ≠ 0 :=
      sub_ne_zero.mpr (boltzmannRootVariable_lt_one hβ (L.prime_mem p hp)).ne'
    simpa [sub_neg_eq_add] using h1.log hne
  have hsum := HasDerivAt.fun_sum hterm
  simpa [souriauEnergy] using hsum.fun_neg

/-- Second derivative of `log Z_P(β)`: `d/dβ souriauEnergy L β = -fisherSouriauSusceptibility L β`. -/
@[rep_depth thermo]
theorem hasDerivAt_souriauEnergy
    (L : FormalPrimeRootLattice) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (souriauEnergy L) (-fisherSouriauSusceptibility L β) β := by
  have hterm : ∀ p ∈ L.primes,
      HasDerivAt
        (fun t : ℝ => Real.log (p : ℝ) * boltzmannRootVariable t p /
          (1 - boltzmannRootVariable t p))
        (-((Real.log (p : ℝ)) ^ 2 * boltzmannRootVariable β p /
          (1 - boltzmannRootVariable β p) ^ 2)) β := by
    intro p hp
    have hnum : HasDerivAt (fun t : ℝ => Real.log (p : ℝ) * boltzmannRootVariable t p)
        (Real.log (p : ℝ) * -(Real.log (p : ℝ) * boltzmannRootVariable β p)) β :=
      (hasDerivAt_boltzmannRootVariable β p).const_mul (Real.log (p : ℝ))
    have hden : HasDerivAt (fun t : ℝ => 1 - boltzmannRootVariable t p)
        (0 - -(Real.log (p : ℝ) * boltzmannRootVariable β p)) β :=
      (hasDerivAt_const β (1 : ℝ)).sub (hasDerivAt_boltzmannRootVariable β p)
    have hne : 1 - boltzmannRootVariable β p ≠ 0 :=
      sub_ne_zero.mpr (boltzmannRootVariable_lt_one hβ (L.prime_mem p hp)).ne'
    have hdiv := hnum.div hden hne
    convert hdiv using 1
    field_simp [hne]
    ring
  change HasDerivAt
      (fun t : ℝ => ∑ p ∈ L.primes,
        Real.log (p : ℝ) * boltzmannRootVariable t p / (1 - boltzmannRootVariable t p))
      (-fisherSouriauSusceptibility L β) β
  simpa [fisherSouriauSusceptibility, Finset.sum_neg_distrib] using
    HasDerivAt.fun_sum hterm

/-- Strict positivity of the Fisher–Souriau susceptibility on any nonempty prime cutoff. -/
@[rep_depth thermo]
theorem fisherSouriauSusceptibility_pos
    (L : FormalPrimeRootLattice) {β : ℝ} (hβ : 0 < β) (hL : L.primes.Nonempty) :
    0 < fisherSouriauSusceptibility L β := by
  unfold fisherSouriauSusceptibility
  refine Finset.sum_pos ?_ hL
  intro p hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (L.prime_mem p hp).one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hpos : 0 < boltzmannRootVariable β p := boltzmannRootVariable_pos β p
  have hsub : 0 < 1 - boltzmannRootVariable β p :=
    sub_pos.mpr (boltzmannRootVariable_lt_one hβ (L.prime_mem p hp))
  positivity

/-- Zero-temperature collapse of the Fisher–Souriau susceptibility:
`χ_P(β) → 0` as `β → +∞`. -/
@[rep_depth thermo]
theorem fisherSouriauSusceptibility_tendsto_zero
    (L : FormalPrimeRootLattice) :
    Filter.Tendsto (fisherSouriauSusceptibility L) Filter.atTop (𝓝 0) := by
  have hterm : ∀ p ∈ L.primes,
      Filter.Tendsto
        (fun β : ℝ => (Real.log (p : ℝ)) ^ 2 * boltzmannRootVariable β p /
          (1 - boltzmannRootVariable β p) ^ 2)
        Filter.atTop (𝓝 0) := by
    intro p hp
    have hb := boltzmannRootVariable_tendsto_zero (L.prime_mem p hp)
    have hnum : Filter.Tendsto
        (fun β : ℝ => (Real.log (p : ℝ)) ^ 2 * boltzmannRootVariable β p)
        Filter.atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (Real.log (p : ℝ)) ^ 2)).mul hb
    have hden : Filter.Tendsto
        (fun β : ℝ => (1 - boltzmannRootVariable β p) ^ 2)
        Filter.atTop (𝓝 1) := by
      have h1 : Filter.Tendsto (fun β : ℝ => 1 - boltzmannRootVariable β p) Filter.atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hb
      simpa using h1.pow 2
    have hdiv := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    simpa [Pi.div_def, zero_div] using hdiv
  change Filter.Tendsto
      (fun β : ℝ => ∑ p ∈ L.primes,
        (Real.log (p : ℝ)) ^ 2 * boltzmannRootVariable β p /
          (1 - boltzmannRootVariable β p) ^ 2)
      Filter.atTop (𝓝 0)
  simpa using tendsto_finsetSum L.primes hterm

end InfoGeometry.Canonical.FormalPrimeRootSystem

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass
import InfoGeometry.Nuclear.NuclearGammaSpectroscopy
import InfoGeometry.Quantum.PenroseOnsagerYangOccupationSpectrum
import InfoGeometry.Quantum.PenroseOnsagerYangOrderParameter
import InfoGeometry.Quantum.PenroseOnsagerYangTwoModeCoherence
import Mathlib.Tactic

/-!
# BCS--BEC Scale-Separation Skeleton

Source context: arXiv:2208.01774v5, "When Superconductivity Crosses Over:
From BCS to BEC" (Chen, Wang, Boyack, Yang, Levin), a review published as
Rev. Mod. Phys. 96, 025002 (2024).

The paper-level physics claim used here is deliberately narrow:

* strict BCS identifies pair formation and condensation at the same temperature;
* BCS--BEC crossover separates the two scales, producing a preformed-pair
  window between condensation and pair formation;
* on the BEC side of the BCS-Leggett ground-state discussion, the fermionic
  chemical potential can be negative, unlike the positive/BCS-side readout.

This file does not formalize superconductivity, a microscopic Hamiltonian,
gap equations, t-matrix theory, KMS dynamics, BEC of prime modes, or any zeta/RH
consequence.  It only records the finite real-order skeleton that can be used
as a theorem-safe interface by downstream thermodynamic modules.
-/

namespace InfoGeometry.Canonical.BCSBECScaleSeparation

noncomputable section

/-- Two temperature scales used in a BCS--BEC crossover readout. -/
structure CrossoverScales where
  /-- Temperature at which pairing / the excitation gap opens. -/
  pairFormationTemp : ℝ
  /-- Temperature at which superconducting/superfluid condensation occurs. -/
  condensationTemp : ℝ

namespace CrossoverScales

/-- Strict BCS scale lock: pairing and condensation occur at the same scale. -/
def IsStrictBCS (S : CrossoverScales) : Prop :=
  S.pairFormationTemp = S.condensationTemp

/-- Crossover scale separation: condensation occurs below pair formation. -/
def IsCrossover (S : CrossoverScales) : Prop :=
  S.condensationTemp < S.pairFormationTemp

/-- The open interval in which pairs are present without condensation. -/
def InPreformedPairWindow (S : CrossoverScales) (T : ℝ) : Prop :=
  S.condensationTemp < T ∧ T < S.pairFormationTemp

/-- The midpoint of the preformed-pair window. -/
def midpointTemp (S : CrossoverScales) : ℝ :=
  (S.condensationTemp + S.pairFormationTemp) / 2

/-- A crossover scale separation is incompatible with strict BCS scale locking. -/
theorem crossover_not_strictBCS
    (S : CrossoverScales) (h : S.IsCrossover) :
    ¬ S.IsStrictBCS := by
  intro hlock
  unfold IsStrictBCS at hlock
  unfold IsCrossover at h
  rw [hlock] at h
  exact (lt_irrefl S.condensationTemp) h

/-- If the crossover scales are separated, the preformed-pair window is nonempty. -/
theorem midpointTemp_mem_preformedPairWindow
    (S : CrossoverScales) (h : S.IsCrossover) :
    S.InPreformedPairWindow S.midpointTemp := by
  unfold InPreformedPairWindow midpointTemp IsCrossover at *
  constructor <;> linarith

/-- The midpoint temperature sits strictly between the two crossover scales. -/
theorem midpointTemp_strictly_between
    (S : CrossoverScales) (h : S.IsCrossover) :
    S.condensationTemp < S.midpointTemp ∧ S.midpointTemp < S.pairFormationTemp := by
  unfold midpointTemp IsCrossover at *
  constructor <;> linarith

/-- Explicit existential version of the preformed-pair window nonemptiness. -/
theorem exists_preformedPairWindow
    (S : CrossoverScales) (h : S.IsCrossover) :
    ∃ T : ℝ, S.InPreformedPairWindow T :=
  ⟨S.midpointTemp, S.midpointTemp_mem_preformedPairWindow h⟩

end CrossoverScales

/-! ## Chemical-potential side readouts -/

/-- BCS-side sign readout for a positive fermionic chemical potential. -/
def IsPositiveChemicalPotential (μ : ℝ) : Prop :=
  0 < μ

/-- BEC-side sign readout for a negative fermionic chemical potential. -/
def IsNegativeChemicalPotential (μ : ℝ) : Prop :=
  μ < 0

/-- Positive and negative chemical-potential side readouts are disjoint. -/
theorem chemicalPotential_sign_readouts_disjoint
    {μ : ℝ} (hpos : IsPositiveChemicalPotential μ) (hneg : IsNegativeChemicalPotential μ) :
    False := by
  unfold IsPositiveChemicalPotential IsNegativeChemicalPotential at *
  linarith

/-- A negative chemical potential cannot simultaneously satisfy the positive-side readout. -/
theorem negativeChemicalPotential_not_positive
    {μ : ℝ} (hneg : IsNegativeChemicalPotential μ) :
    ¬ IsPositiveChemicalPotential μ := by
  intro hpos
  exact chemicalPotential_sign_readouts_disjoint hpos hneg

/-! ## Crossover Scale Ratios & Margins -/

namespace CrossoverScales

/-- Any temperature in the preformed-pair window witnesses crossover scale separation. -/
theorem inPreformedPairWindow_implies_isCrossover
    {S : CrossoverScales} {T : ℝ} (hT : S.InPreformedPairWindow T) :
    S.IsCrossover := by
  unfold InPreformedPairWindow at hT
  unfold IsCrossover
  linarith

/-- Under strict BCS scale locking (`T^* = T_c`), the preformed-pair window is empty. -/
theorem strictBCS_preformedPairWindow_empty
    {S : CrossoverScales} (hBCS : S.IsStrictBCS) (T : ℝ) :
    ¬ S.InPreformedPairWindow T := by
  intro hT
  exact S.crossover_not_strictBCS (inPreformedPairWindow_implies_isCrossover hT) hBCS

/-- Dimensionless scale ratio characterization of crossover (`T^*/T_c > 1`) vs strict BCS (`T^*/T_c = 1`). -/
theorem crossover_scale_ratio_gt_one
    {S : CrossoverScales} (hTc : 0 < S.condensationTemp) :
    (S.IsCrossover ↔ 1 < S.pairFormationTemp / S.condensationTemp) ∧
      (S.IsStrictBCS ↔ S.pairFormationTemp / S.condensationTemp = 1) := by
  unfold IsCrossover IsStrictBCS
  constructor
  · exact (one_lt_div hTc).symm
  · exact (div_eq_one_iff_eq (ne_of_gt hTc)).symm

/-- The midpoint temperature bisects the preformed-pair window symmetrically. -/
theorem midpointTemp_symmetric_margins (S : CrossoverScales) :
    S.pairFormationTemp - S.midpointTemp = S.midpointTemp - S.condensationTemp ∧
      S.midpointTemp - S.condensationTemp = (S.pairFormationTemp - S.condensationTemp) / 2 := by
  unfold midpointTemp
  constructor <;> ring

end CrossoverScales

/-! ## Leggett BCS–BEC Quasiparticle Gap Dichotomy & Uniform Schur-Denominator Invertibility -/

open InfoGeometry.Physics.NuclearBdGTwoLevelExact

/-- For any single-particle energy `ε`, chemical potential `μ`, and pairing `Δ`, the BdG
quasiparticle energy is bounded below by `|Δ|`. -/
theorem bcs_bdgEnergy_ge_abs_delta (ε μ Δ : ℝ) :
    |Δ| ≤ bdgEnergy (ε - μ) Δ := by
  rw [← Real.sqrt_sq_eq_abs Δ]
  apply Real.sqrt_le_sqrt
  linarith [sq_nonneg (ε - μ)]

/-- Generalized finite-spectrum BCS lower bound and uniform Schur-complement invertibility:
over any nonempty mode shell `s : Finset κ`, the minimal BdG energy is bounded below by `|Δ|`,
and `bdgBlock (ε k - μ) Δ - E • 1` is invertible uniformly for all `k ∈ s` and `|E| < |Δ|`. -/
theorem bcs_spectrum_gap_ge_abs_delta
    {κ : Type*} (ε : κ → ℝ) (s : Finset κ) (hs : s.Nonempty) (μ Δ : ℝ) :
    |Δ| ≤ s.inf' hs (fun k => bdgEnergy (ε k - μ) Δ) ∧
      ∀ k ∈ s, ∀ E : ℝ, |E| < |Δ| →
        (bdgBlock (ε k - μ) Δ - E • (1 : M2R)).det ≠ 0 := by
  refine ⟨Finset.le_inf' hs _ fun k _ => bcs_bdgEnergy_ge_abs_delta (ε k) μ Δ, ?_⟩
  intro k hk E hE
  have hInf : |Δ| ≤ s.inf' hs (fun j => bdgEnergy (ε j - μ) Δ) :=
    Finset.le_inf' hs _ fun j _ => bcs_bdgEnergy_ge_abs_delta (ε j) μ Δ
  have hk_lt : |E| < bdgEnergy (ε k - μ) Δ :=
    lt_of_lt_of_le (lt_of_lt_of_le hE hInf) (Finset.inf'_le (fun j => bdgEnergy (ε j - μ) Δ) hk)
  rw [bdg_characteristic]
  have h2 : |E| ^ 2 < (bdgEnergy (ε k - μ) Δ) ^ 2 :=
    sq_lt_sq' (by linarith [abs_nonneg E, bdgEnergy_nonneg (ε k - μ) Δ]) hk_lt
  rw [sq_abs, bdgEnergy_sq] at h2
  exact sub_ne_zero.mpr (ne_of_lt h2)

/-- On the BCS side (`0 < μ`), the Fermi surface `ε = μ ≥ 0` attains the minimal gap `|Δ|`. -/
theorem bcs_fermi_surface_attains_min_gap
    {μ : ℝ} (hμ : IsPositiveChemicalPotential μ) (Δ : ℝ) :
    ∃ ε : ℝ, 0 ≤ ε ∧ bdgEnergy (ε - μ) Δ = |Δ| := by
  refine ⟨μ, le_of_lt hμ, ?_⟩
  simp [bdgEnergy, Real.sqrt_sq_eq_abs]

/-- On the BEC side (`μ < 0`), for every nonnegative kinetic energy `0 ≤ ε`, the quasiparticle
energy is bounded below by its `ε = 0` threshold `bdgEnergy μ Δ = √(μ² + Δ²)`. -/
theorem bec_bdgEnergy_ge_zero_kinetic
    {ε μ : ℝ} (hμ : IsNegativeChemicalPotential μ) (hε : 0 ≤ ε) (Δ : ℝ) :
    bdgEnergy μ Δ ≤ bdgEnergy (ε - μ) Δ := by
  unfold IsNegativeChemicalPotential at hμ
  unfold bdgEnergy
  apply Real.sqrt_le_sqrt
  have hsq : μ ^ 2 ≤ (ε - μ) ^ 2 := by
    have hdiff : (ε - μ) ^ 2 - μ ^ 2 = ε * (ε - 2 * μ) := by ring
    have hnonneg : 0 ≤ ε * (ε - 2 * μ) := mul_nonneg hε (by linarith)
    linarith
  linarith

/-- On the BEC side (`μ < 0`), the minimal gap `√(μ² + Δ²)` is strictly larger than `|Δ|`. -/
theorem bec_min_gap_strictly_gt_abs_delta
    {μ : ℝ} (hμ : IsNegativeChemicalPotential μ) (Δ : ℝ) :
    |Δ| < bdgEnergy μ Δ := by
  rw [← Real.sqrt_sq_eq_abs Δ]
  apply Real.sqrt_lt_sqrt (sq_nonneg Δ)
  have hμsq : 0 < μ ^ 2 := sq_pos_of_ne_zero (ne_of_lt hμ)
  linarith

/-- Generalized finite-spectrum BEC lower bound (`μ < 0`, `0 ≤ ε k` on `s`): the shell
quasiparticle gap strictly exceeds `|Δ|`, is bounded below by `bdgEnergy μ Δ` across `s`,
and keeps `bdgBlock (ε k - μ) Δ - E • 1` uniformly invertible for all `k ∈ s` and
`|E| < bdgEnergy μ Δ`. -/
theorem bec_spectrum_gap_ge_zero_kinetic
    {κ : Type*} (ε : κ → ℝ) (s : Finset κ) (hs : s.Nonempty)
    (hε : ∀ k ∈ s, 0 ≤ ε k)
    {μ : ℝ} (hμ : IsNegativeChemicalPotential μ) (Δ : ℝ) :
    |Δ| < bdgEnergy μ Δ ∧
      bdgEnergy μ Δ ≤ s.inf' hs (fun k => bdgEnergy (ε k - μ) Δ) ∧
      ∀ k ∈ s, ∀ E : ℝ, |E| < bdgEnergy μ Δ →
        (bdgBlock (ε k - μ) Δ - E • (1 : M2R)).det ≠ 0 := by
  have hInf : bdgEnergy μ Δ ≤ s.inf' hs (fun k => bdgEnergy (ε k - μ) Δ) :=
    Finset.le_inf' hs _ fun k hk => bec_bdgEnergy_ge_zero_kinetic hμ (hε k hk) Δ
  refine ⟨bec_min_gap_strictly_gt_abs_delta hμ Δ, hInf, ?_⟩
  intro k hk E hE
  have hk_lt : |E| < bdgEnergy (ε k - μ) Δ :=
    lt_of_lt_of_le (lt_of_lt_of_le hE hInf) (Finset.inf'_le (fun j => bdgEnergy (ε j - μ) Δ) hk)
  rw [bdg_characteristic]
  have h2 : |E| ^ 2 < (bdgEnergy (ε k - μ) Δ) ^ 2 :=
    sq_lt_sq' (by linarith [abs_nonneg E, bdgEnergy_nonneg (ε k - μ) Δ]) hk_lt
  rw [sq_abs, bdgEnergy_sq] at h2
  exact sub_ne_zero.mpr (ne_of_lt h2)

/-- On the BEC side (`μ < 0`), the quasiparticle gap remains strictly positive (`-μ > 0`)
even when the pairing amplitude `Δ` vanishes. -/
theorem bec_gap_positive_even_at_zero_pairing
    {μ : ℝ} (hμ : IsNegativeChemicalPotential μ) :
    0 < bdgEnergy μ 0 ∧ bdgEnergy μ 0 = -μ := by
  unfold IsNegativeChemicalPotential at hμ
  have heq : bdgEnergy μ 0 = -μ := by
    simp [bdgEnergy, Real.sqrt_sq_eq_abs, abs_of_neg hμ]
  exact ⟨by linarith, heq⟩

/-- Inside the BCS gap (`|E| < |Δ|`), the two-level BdG Schur-complement denominator
`bdgBlock (ε - μ) Δ - E • 1` is uniformly invertible across all kinetic energies `ε` and
chemical potentials `μ`. -/
theorem bcs_continuum_bdg_det_ne_zero
    {E Δ : ℝ} (hE : |E| < |Δ|) (ε μ : ℝ) :
    (bdgBlock (ε - μ) Δ - E • (1 : M2R)).det ≠ 0 := by
  rw [bdg_characteristic]
  have hEsq : E ^ 2 < Δ ^ 2 := sq_lt_sq.mpr hE
  have hlt : E ^ 2 < (ε - μ) ^ 2 + Δ ^ 2 := by linarith [sq_nonneg (ε - μ)]
  exact sub_ne_zero.mpr (ne_of_lt hlt)

/-- Inside the BEC threshold gap (`|E| < bdgEnergy μ Δ`, `μ < 0`), the two-level BdG
Schur-complement denominator `bdgBlock (ε - μ) Δ - E • 1` is uniformly invertible across the
entire nonnegative kinetic-energy continuum `0 ≤ ε`. -/
theorem bec_continuum_bdg_det_ne_zero
    {E μ Δ : ℝ} (hμ : IsNegativeChemicalPotential μ)
    (hE : |E| < bdgEnergy μ Δ) {ε : ℝ} (hε : 0 ≤ ε) :
    (bdgBlock (ε - μ) Δ - E • (1 : M2R)).det ≠ 0 := by
  rw [bdg_characteristic]
  have h1 : |E| < bdgEnergy (ε - μ) Δ :=
    lt_of_lt_of_le hE (bec_bdgEnergy_ge_zero_kinetic hμ hε Δ)
  have h2 : |E| ^ 2 < (bdgEnergy (ε - μ) Δ) ^ 2 :=
    sq_lt_sq' (by linarith [abs_nonneg E, bdgEnergy_nonneg (ε - μ) Δ]) h1
  rw [sq_abs, bdgEnergy_sq] at h2
  exact sub_ne_zero.mpr (ne_of_lt h2)

/-! ## Two-Gap Decomposition (`Δ² = Δ_sc² + Δ_pg²`), Vortex Mass `4Δ²`, & POY Condensation Bridge -/

section TwoGapVortexPOYBridge

open InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass
open InfoGeometry.Nuclear.GammaSpectroscopy
open InfoGeometry.Quantum.PenroseOnsagerYang

/-- Two-gap BCS–BEC crossover decomposition `Δ² = Δ_sc² + Δ_pg²` (Chen–Wang–Boyack–Yang–Levin):
`deltaSC` measures the phase-coherent superconducting condensate gap and `deltaPG` measures the
non-condensed preformed-pair pseudogap. -/
structure TwoGapDecomposition where
  deltaSC : ℝ
  deltaPG : ℝ
  deltaSC_nonneg : 0 ≤ deltaSC
  deltaPG_nonneg : 0 ≤ deltaPG

namespace TwoGapDecomposition

/-- Total squared pairing gap `Δ² = Δ_sc² + Δ_pg²`. -/
def totalGapSq (g : TwoGapDecomposition) : ℝ :=
  g.deltaSC ^ 2 + g.deltaPG ^ 2

/-- Total pairing gap `Δ = √(Δ_sc² + Δ_pg²)`. -/
def totalGap (g : TwoGapDecomposition) : ℝ :=
  Real.sqrt g.totalGapSq

/-- Nonnegativity of `totalGapSq`. -/
theorem totalGapSq_nonneg (g : TwoGapDecomposition) : 0 ≤ g.totalGapSq := by
  unfold totalGapSq
  positivity

/-- Squaring `totalGap` recovers `totalGapSq = Δ_sc² + Δ_pg²`. -/
theorem totalGap_sq (g : TwoGapDecomposition) : g.totalGap ^ 2 = g.totalGapSq := by
  unfold totalGap
  rw [Real.sq_sqrt g.totalGapSq_nonneg]

end TwoGapDecomposition

/-- Concrete witness inhabiting `TwoGapDecomposition` (`Δ_sc = 1, Δ_pg = 1`). -/
def twoGapConcreteWitness : TwoGapDecomposition where
  deltaSC := 1
  deltaPG := 1
  deltaSC_nonneg := zero_le_one
  deltaPG_nonneg := zero_le_one

/-- Instantiate `CrossoverScales` from a `TwoGapDecomposition` with base scale `T_base` and
stiffness-to-temperature slope `c_scale`:
- `condensationTemp = T_base + c_scale * Δ_sc²` (`T_c`)
- `pairFormationTemp = T_base + c_scale * (Δ_sc² + Δ_pg²)` (`T^*`). -/
def twoGapCrossoverScales (T_base c_scale : ℝ) (g : TwoGapDecomposition) : CrossoverScales where
  pairFormationTemp := T_base + c_scale * g.totalGapSq
  condensationTemp := T_base + c_scale * g.deltaSC ^ 2

theorem twoGapCrossoverScales_gap_diff (T_base c_scale : ℝ) (g : TwoGapDecomposition) :
    (twoGapCrossoverScales T_base c_scale g).pairFormationTemp -
      (twoGapCrossoverScales T_base c_scale g).condensationTemp =
      c_scale * g.deltaPG ^ 2 := by
  simp [twoGapCrossoverScales, TwoGapDecomposition.totalGapSq]
  ring

/-- Whenever `Δ_pg > 0` (with positive slope `c_scale > 0`), the two-gap crossover scales strictly
separate (`T_c < T^*`), opening a nonempty `InPreformedPairWindow` and ruling out `IsStrictBCS`. -/
theorem twoGap_opens_preformedPairWindow
    {T_base c_scale : ℝ} (hc : 0 < c_scale)
    {g : TwoGapDecomposition} (hpg : 0 < g.deltaPG) :
    let S := twoGapCrossoverScales T_base c_scale g
    S.IsCrossover ∧
    ¬ S.IsStrictBCS ∧
    S.InPreformedPairWindow S.midpointTemp ∧
    (∃ T : ℝ, S.InPreformedPairWindow T) := by
  intro S
  have hDiff : 0 < S.pairFormationTemp - S.condensationTemp := by
    rw [twoGapCrossoverScales_gap_diff]
    exact mul_pos hc (sq_pos_of_pos hpg)
  have hCross : S.IsCrossover := by
    unfold CrossoverScales.IsCrossover
    linarith
  exact ⟨hCross, S.crossover_not_strictBCS hCross,
    S.midpointTemp_mem_preformedPairWindow hCross, S.exists_preformedPairWindow hCross⟩

/-- Whenever the pseudogap vanishes (`Δ_pg = 0`), the two-gap crossover scales collapse to
`IsStrictBCS` (`T^* = T_c`), emptying `InPreformedPairWindow`. -/
theorem twoGap_strictBCS_of_pseudogap_zero
    (T_base c_scale : ℝ) {g : TwoGapDecomposition} (hpg : g.deltaPG = 0) :
    let S := twoGapCrossoverScales T_base c_scale g
    S.IsStrictBCS ∧
    (∀ T : ℝ, ¬ S.InPreformedPairWindow T) ∧
    g.totalGapSq = g.deltaSC ^ 2 := by
  intro S
  have hEq : S.pairFormationTemp = S.condensationTemp := by
    have hDiff := twoGapCrossoverScales_gap_diff T_base c_scale g
    rw [hpg, zero_pow (by norm_num), mul_zero] at hDiff
    linarith
  exact ⟨hEq, S.strictBCS_preformedPairWindow_empty hEq,
    by simp [TwoGapDecomposition.totalGapSq, hpg]⟩

/-- Links a `NuclearBCSPairing` gap `Δ = bcs.pairingGap` satisfying `Δ² = Δ_sc² + Δ_pg²` to
both `NuclearGammaSpectroscopy.quasiparticleEnergy` and the `2 × 2` Nambu Peirce defect vortex mass
`opVortexMassSq = (4 * Δ²) • 1` from `TwoSheetedNilpotentCondensateVortexMass`. -/
theorem nuclearBCS_twoGap_vortexMass_bridge
    (bcs : NuclearBCSPairing) (g : TwoGapDecomposition)
    (hMatch : g.totalGapSq = bcs.pairingGap ^ 2) :
    g.totalGap = bcs.pairingGap ∧
    g.totalGap ≤ quasiparticleEnergy bcs ∧
    opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap)) =
      (4 * bcs.pairingGap ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    nambuProj *
        opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap)) *
        nambuProj =
      (4 * bcs.pairingGap ^ 2) • nambuProj := by
  have hGap : g.totalGap = bcs.pairingGap := by
    unfold TwoGapDecomposition.totalGap
    rw [hMatch, Real.sqrt_sq bcs.hGap_pos.le]
  have hNambu := nambu_particle_hole_vortex_mass_realization g.totalGap
  have hQp := quasiparticleEnergy_ge_gap bcs
  rw [← hGap] at hQp
  refine ⟨hGap, hQp, ?_, ?_⟩
  · rw [hNambu.2.2.2.2.2.2.1, hGap]
  · rw [hNambu.2.2.2.2.2.2.2.1, hGap]

/-- Explicit Penrose–Onsager–Yang coherent occupation family (`N₀(N) = N · (‖a‖² + ‖b‖²)`, `N₁ = 0`). -/
private def scaleSepCoherentFamily (a b : ℂ) : OccupationFamily (Fin 2) where
  occupation N i := match i with
    | 0 => (N : ℝ) * (Complex.normSq a + Complex.normSq b)
    | 1 => 0
  occupation_nonneg N i := by
    fin_cases i
    · exact mul_nonneg (Nat.cast_nonneg N)
        (add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b))
    · exact le_rfl

/-- Explicit Penrose–Onsager–Yang fragmented Fock occupation family (`N₀ = N · ‖a‖²`, `N₁ = N · ‖b‖²`). -/
private def scaleSepFragmentedFamily (a b : ℂ) : OccupationFamily (Fin 2) where
  occupation N i := match i with
    | 0 => (N : ℝ) * Complex.normSq a
    | 1 => (N : ℝ) * Complex.normSq b
  occupation_nonneg N i := by
    fin_cases i
    · exact mul_nonneg (Nat.cast_nonneg N) (Complex.normSq_nonneg a)
    · exact mul_nonneg (Nat.cast_nonneg N) (Complex.normSq_nonneg b)

/-- **Master Bridge Theorem: Two-Sheeted Peirce Vortex Mass (`4 Δ²`), Penrose–Onsager–Yang
Simple vs. Fragmented Condensation, and BCS (`μ > 0`) vs. BEC (`μ < 0`) Scale Separation**:
Unifies:
1. Two-sheeted Nambu Peirce vortex mass `4(Δ_sc² + Δ_pg²) • 1` (and upper-sheet `4Δ² • P`),
   positive definite whenever `bcs.pairingGap > 0`,
2. Penrose–Onsager–Yang separation between coherent simple condensation (`IsSimpleCondensate`)
   and incoherent Fock fragmentation (`IsFragmentedCondensate`) matching `coherentTwoModeKernel` vs
   `incoherentKernelOfAmplitudes`,
3. Two-gap scale separation (`Δ_pg > 0 → InPreformedPairWindow` nonempty; `Δ_pg = 0 → IsStrictBCS`),
4. Disjoint BCS (`μ_bcs > 0`, Fermi-surface gap minimum `Δ`) vs BEC (`μ_bec < 0`, gapped above
   `√(μ_bec² + Δ²) > Δ` for all `0 ≤ ε`) regimes. -/
theorem twoSheeted_vortexMass_poy_bcs_bec_unification
    (bcs : NuclearBCSPairing) (g : TwoGapDecomposition)
    (hMatch : g.totalGapSq = bcs.pairingGap ^ 2)
    {T_base c_scale : ℝ} (hc : 0 < c_scale)
    {a b : ℂ} (hab : a * starRingEnd ℂ b ≠ 0)
    {μ_bcs μ_bec : ℝ}
    (hμ_bcs : IsPositiveChemicalPotential μ_bcs)
    (hμ_bec : IsNegativeChemicalPotential μ_bec) :
    (opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap)) =
        (4 * (g.deltaSC ^ 2 + g.deltaPG ^ 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      nambuProj *
          opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap)) *
          nambuProj =
        (4 * bcs.pairingGap ^ 2) • nambuProj ∧
      ∀ v : Fin 2 → ℝ, v ≠ 0 →
        0 < star v ⬝ᵥ
          (opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap))).mulVec v) ∧
    (∃ F_coh F_frag : OccupationFamily (Fin 2),
      IsSimpleCondensate F_coh ∧ ¬ IsFragmentedCondensate F_coh ∧
      IsFragmentedCondensate F_frag ∧ ¬ IsSimpleCondensate F_frag ∧
      coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b) ∧
    ((0 < g.deltaPG →
        (twoGapCrossoverScales T_base c_scale g).IsCrossover ∧
        (twoGapCrossoverScales T_base c_scale g).InPreformedPairWindow
          (twoGapCrossoverScales T_base c_scale g).midpointTemp) ∧
      (g.deltaPG = 0 → (twoGapCrossoverScales T_base c_scale g).IsStrictBCS)) ∧
    (¬ IsPositiveChemicalPotential μ_bec ∧
      (∃ ε : ℝ, 0 ≤ ε ∧ bdgEnergy (ε - μ_bcs) bcs.pairingGap = bcs.pairingGap) ∧
      (∀ ε : ℝ, 0 ≤ ε →
        bcs.pairingGap < bdgEnergy μ_bec bcs.pairingGap ∧
        bdgEnergy μ_bec bcs.pairingGap ≤ bdgEnergy (ε - μ_bec) bcs.pairingGap)) := by
  have hVortex := nuclearBCS_twoGap_vortexMass_bridge bcs g hMatch
  have hNambu := nambu_particle_hole_vortex_mass_realization g.totalGap
  have hGapNe : g.totalGap ≠ 0 := by
    rw [hVortex.1]
    exact bcs.hGap_pos.ne'
  have hVortexPart :
      opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap)) =
          (4 * (g.deltaSC ^ 2 + g.deltaPG ^ 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
        nambuProj *
            opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap)) *
            nambuProj =
          (4 * bcs.pairingGap ^ 2) • nambuProj ∧
        ∀ v : Fin 2 → ℝ, v ≠ 0 →
          0 < star v ⬝ᵥ
            (opVortexMassSq nambuProj (nambuGapGen g.totalGap) (star (nambuGapGen g.totalGap))).mulVec v := by
    refine ⟨?_, hVortex.2.2.2, hNambu.2.2.2.2.2.2.2.2 hGapNe⟩
    rw [hVortex.2.2.1, ← hMatch, TwoGapDecomposition.totalGapSq]
  have ha : a ≠ 0 := fun h0 => hab (by simp [h0])
  have hb : b ≠ 0 := fun h0 => hab (by simp [h0])
  have hPOY :
      ∃ F_coh F_frag : OccupationFamily (Fin 2),
        IsSimpleCondensate F_coh ∧ ¬ IsFragmentedCondensate F_coh ∧
        IsFragmentedCondensate F_frag ∧ ¬ IsSimpleCondensate F_frag ∧
        coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b := by
    refine ⟨scaleSepCoherentFamily a b, scaleSepFragmentedFamily a b, ?_, ?_, ?_, ?_,
      coherent_ne_incoherent_of_cross_ne_zero hab⟩
    · have hm0 : IsMacroscopicMode (scaleSepCoherentFamily a b) 0 := by
        refine ⟨Complex.normSq a + Complex.normSq b,
          add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr ha) (Complex.normSq_nonneg b),
          Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩⟩
        simp only [scaledOccupation, scaleSepCoherentFamily, populationScale]
        have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
        rw [mul_div_cancel_left₀ _ hpos.ne']
      have hnot1 : ¬ IsMacroscopicMode (scaleSepCoherentFamily a b) 1 := by
        rintro ⟨c, hc, hEv⟩
        rcases Filter.eventually_atTop.mp hEv with ⟨N₀, hN₀⟩
        have hle := hN₀ N₀ (le_refl N₀)
        simp [scaledOccupation, scaleSepCoherentFamily] at hle
        linarith
      refine ⟨0, hm0, fun j hj => ?_⟩
      fin_cases j
      · rfl
      · exact (hnot1 hj).elim
    · refine simple_not_fragmented ?_
      have hm0 : IsMacroscopicMode (scaleSepCoherentFamily a b) 0 := by
        refine ⟨Complex.normSq a + Complex.normSq b,
          add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr ha) (Complex.normSq_nonneg b),
          Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩⟩
        simp only [scaledOccupation, scaleSepCoherentFamily, populationScale]
        have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
        rw [mul_div_cancel_left₀ _ hpos.ne']
      have hnot1 : ¬ IsMacroscopicMode (scaleSepCoherentFamily a b) 1 := by
        rintro ⟨c, hc, hEv⟩
        rcases Filter.eventually_atTop.mp hEv with ⟨N₀, hN₀⟩
        have hle := hN₀ N₀ (le_refl N₀)
        simp [scaledOccupation, scaleSepCoherentFamily] at hle
        linarith
      exact ⟨0, hm0, fun j hj => by fin_cases j; rfl; exact (hnot1 hj).elim⟩
    · have hm0 : IsMacroscopicMode (scaleSepFragmentedFamily a b) 0 := by
        refine ⟨Complex.normSq a, Complex.normSq_pos.mpr ha,
          Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩⟩
        simp only [scaledOccupation, scaleSepFragmentedFamily, populationScale]
        have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
        rw [mul_div_cancel_left₀ _ hpos.ne']
      have hm1 : IsMacroscopicMode (scaleSepFragmentedFamily a b) 1 := by
        refine ⟨Complex.normSq b, Complex.normSq_pos.mpr hb,
          Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩⟩
        simp only [scaledOccupation, scaleSepFragmentedFamily, populationScale]
        have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
        rw [mul_div_cancel_left₀ _ hpos.ne']
      exact ⟨0, 1, by decide, hm0, hm1⟩
    · intro hS
      have hm0 : IsMacroscopicMode (scaleSepFragmentedFamily a b) 0 := by
        refine ⟨Complex.normSq a, Complex.normSq_pos.mpr ha,
          Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩⟩
        simp only [scaledOccupation, scaleSepFragmentedFamily, populationScale]
        have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
        rw [mul_div_cancel_left₀ _ hpos.ne']
      have hm1 : IsMacroscopicMode (scaleSepFragmentedFamily a b) 1 := by
        refine ⟨Complex.normSq b, Complex.normSq_pos.mpr hb,
          Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩⟩
        simp only [scaledOccupation, scaleSepFragmentedFamily, populationScale]
        have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
        rw [mul_div_cancel_left₀ _ hpos.ne']
      exact simple_not_fragmented hS ⟨0, 1, by decide, hm0, hm1⟩
  have hScales :
      (0 < g.deltaPG →
          (twoGapCrossoverScales T_base c_scale g).IsCrossover ∧
          (twoGapCrossoverScales T_base c_scale g).InPreformedPairWindow
            (twoGapCrossoverScales T_base c_scale g).midpointTemp) ∧
        (g.deltaPG = 0 → (twoGapCrossoverScales T_base c_scale g).IsStrictBCS) := by
    constructor
    · intro hpg
      have hW := twoGap_opens_preformedPairWindow (T_base := T_base) hc hpg
      exact ⟨hW.1, hW.2.2.1⟩
    · intro hpg
      exact (twoGap_strictBCS_of_pseudogap_zero T_base c_scale hpg).1
  have hBCS_BEC :
      ¬ IsPositiveChemicalPotential μ_bec ∧
      (∃ ε : ℝ, 0 ≤ ε ∧ bdgEnergy (ε - μ_bcs) bcs.pairingGap = bcs.pairingGap) ∧
      (∀ ε : ℝ, 0 ≤ ε →
        bcs.pairingGap < bdgEnergy μ_bec bcs.pairingGap ∧
        bdgEnergy μ_bec bcs.pairingGap ≤ bdgEnergy (ε - μ_bec) bcs.pairingGap) := by
    refine ⟨negativeChemicalPotential_not_positive hμ_bec, ?_, ?_⟩
    · rcases bcs_fermi_surface_attains_min_gap hμ_bcs bcs.pairingGap with ⟨ε, hε, hEq⟩
      rw [abs_of_pos bcs.hGap_pos] at hEq
      exact ⟨ε, hε, hEq⟩
    · intro ε hε
      have h1 := bec_min_gap_strictly_gt_abs_delta hμ_bec bcs.pairingGap
      rw [abs_of_pos bcs.hGap_pos] at h1
      exact ⟨h1, bec_bdgEnergy_ge_zero_kinetic hμ_bec hε bcs.pairingGap⟩
  exact ⟨hVortexPart, hPOY, hScales, hBCS_BEC⟩

end TwoGapVortexPOYBridge

end

end InfoGeometry.Canonical.BCSBECScaleSeparation

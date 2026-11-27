/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.PenroseOnsagerYangOccupationSpectrum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.PenroseOnsagerYangOrderParameter
import InfoGeometry.Quantum.PenroseOnsagerYangTwoModeCoherence
import InfoGeometry.Canonical.BCSBECScaleSeparation
import InfoGeometry.Physics.NuclearBdGBogoliubovCAR

/-!
# Penrose--Onsager--Yang finite condensation chain

This capstone packages only the intrinsic finite mathematics:

* macroscopic occupation is linear-scale spectral occupation;
* simple and fragmented condensation are distinct predicates;
* `sqrt(N0) chi` has squared norm and rank-one-kernel trace `N0`;
* a global scalar phase disappears from the rank-one kernel;
* coherent and diagonal two-mode kernels can have identical diagonal
  occupations while differing in off-diagonal coherence.

It does not identify these facts with spontaneous `U(1)` breaking, a BdG
Hamiltonian, Majorana modes, an ODLRO spatial limit, or a transport law.
-/

noncomputable section

namespace InfoGeometry.Canonical.PenroseOnsagerYangCondensationPristineChain

open scoped BigOperators ComplexOrder
open InfoGeometry.Quantum.PenroseOnsagerYang

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- Exact classification statement: a simply condensed occupation family is
not fragmented. -/
theorem pristine_simple_fragmented_separation
    {F : OccupationFamily κ}
    (hF : IsSimpleCondensate F) :
    ¬ IsFragmentedCondensate F :=
  simple_not_fragmented hF

/-- Exact finite order-parameter statement. -/
theorem pristine_orderParameter_kernel
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    {χ : Mode ι} (hχ : IsNormalizedMode χ)
    {u : ℂ} (hu : u * starRingEnd ℂ u = 1) :
    (rankOneKernel χ).PosSemidef ∧
      (rankOneKernel χ).IsHermitian ∧
      modeNormSq (orderParameter N0 χ) = N0 ∧
      Matrix.trace (rankOneKernel (orderParameter N0 χ)) = (N0 : ℂ) ∧
      rankOneKernel (scalarAction u χ) = rankOneKernel χ :=
  condensate_kernel_packet hN0 hχ hu

/-- Exact finite spectral-kernel statement. -/
theorem pristine_spectralKernel
    (occupation : κ → ℝ)
    (hoccupation : ∀ k, 0 ≤ occupation k)
    (mode : κ → Mode ι)
    (hmode : ∀ k, IsNormalizedMode (mode k)) :
    (spectralKernel occupation mode).PosSemidef ∧
      Matrix.trace (spectralKernel occupation mode) =
        ∑ k, (occupation k : ℂ) := by
  exact ⟨spectralKernel_posSemidef occupation mode,
    trace_spectralKernel occupation hoccupation mode hmode⟩

/-- Exact finite coherent/diagonal two-mode separation. -/
theorem pristine_twoMode_coherence
    {a b : ℂ} (hab : a * starRingEnd ℂ b ≠ 0) :
    Matrix.det (coherentTwoModeKernel a b) = 0 ∧
      (coherentTwoModeKernel a b).PosSemidef ∧
      (incoherentKernelOfAmplitudes a b).PosSemidef ∧
      coherentTwoModeKernel a b 0 0 =
        incoherentKernelOfAmplitudes a b 0 0 ∧
      coherentTwoModeKernel a b 1 1 =
        incoherentKernelOfAmplitudes a b 1 1 ∧
      coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b :=
  twoMode_coherence_packet hab

/-- Combined theorem-safe Penrose--Onsager--Yang packet. -/
theorem penrose_onsager_yang_condensation_pristine_chain
    {F : OccupationFamily κ}
    (hF : IsSimpleCondensate F)
    (occupation : κ → ℝ)
    (hoccupation : ∀ k, 0 ≤ occupation k)
    (mode : κ → Mode ι)
    (hmode : ∀ k, IsNormalizedMode (mode k))
    {N0 : ℝ} (hN0 : 0 ≤ N0)
    {χ : Mode ι} (hχ : IsNormalizedMode χ)
    {u : ℂ} (hu : u * starRingEnd ℂ u = 1)
    {a b : ℂ} (hab : a * starRingEnd ℂ b ≠ 0) :
    (¬ IsFragmentedCondensate F) ∧
      (spectralKernel occupation mode).PosSemidef ∧
      Matrix.trace (spectralKernel occupation mode) =
        ∑ k, (occupation k : ℂ) ∧
      modeNormSq (orderParameter N0 χ) = N0 ∧
      Matrix.trace (rankOneKernel (orderParameter N0 χ)) = (N0 : ℂ) ∧
      rankOneKernel (scalarAction u χ) = rankOneKernel χ ∧
      (incoherentKernelOfAmplitudes a b).PosSemidef ∧
      coherentTwoModeKernel a b ≠ incoherentKernelOfAmplitudes a b := by
  exact ⟨simple_not_fragmented hF,
    spectralKernel_posSemidef occupation mode,
    trace_spectralKernel occupation hoccupation mode hmode,
    modeNormSq_orderParameter hN0 hχ,
    trace_orderParameterKernel hN0 hχ,
    rankOneKernel_globalPhase_invariant hu χ,
    incoherentKernelOfAmplitudes_posSemidef a b,
    coherent_ne_incoherent_of_cross_ne_zero hab⟩

/-! ## Condensation Regimes Across `BCSBECScaleSeparation.CrossoverScales` -/

section BCSBECPhaseBridge

open InfoGeometry.Canonical.BCSBECScaleSeparation

/-- A temperature-indexed occupation family on an arbitrary mode type `κ` has simple
condensation everywhere below `S.condensationTemp`. -/
def HasSimpleCondensationBelowTc
    (S : CrossoverScales) (F_of_T : ℝ → OccupationFamily κ) : Prop :=
  ∀ T : ℝ, T < S.condensationTemp → IsSimpleCondensate (F_of_T T)

/-- A temperature-indexed occupation family on an arbitrary mode type `κ` is in the normal
(uncondensed) phase everywhere above `S.condensationTemp`. -/
def HasNormalStateAboveTc
    (S : CrossoverScales) (F_of_T : ℝ → OccupationFamily κ) : Prop :=
  ∀ T : ℝ, S.condensationTemp < T → IsNormalFamily (F_of_T T)

omit [DecidableEq κ] in
/-- Inside the preformed-pair window (`T_c < T < T^*`), an occupation family that is normal
above `T_c` exhibits neither simple nor fragmented condensation. -/
theorem preformedPairWindow_no_simple_or_fragmented_condensate
    {S : CrossoverScales} {F_of_T : ℝ → OccupationFamily κ} {T : ℝ}
    (hNorm : HasNormalStateAboveTc S F_of_T)
    (hWin : S.InPreformedPairWindow T) :
    IsNormalFamily (F_of_T T) ∧
      ¬ IsSimpleCondensate (F_of_T T) ∧
      ¬ IsFragmentedCondensate (F_of_T T) := by
  have hN : IsNormalFamily (F_of_T T) := hNorm T hWin.1
  exact ⟨hN, normal_not_simple hN, normal_not_fragmented hN⟩

omit [DecidableEq κ] in
/-- In any crossover regime (`T_c < T^*`), the midpoint temperature sits in the preformed-pair
window and has neither simple nor fragmented condensation. -/
theorem crossover_midpoint_in_preformed_normal_regime
    {S : CrossoverScales} {F_of_T : ℝ → OccupationFamily κ}
    (hCross : S.IsCrossover) (hNorm : HasNormalStateAboveTc S F_of_T) :
    S.InPreformedPairWindow S.midpointTemp ∧
      IsNormalFamily (F_of_T S.midpointTemp) ∧
      ¬ IsSimpleCondensate (F_of_T S.midpointTemp) ∧
      ¬ IsFragmentedCondensate (F_of_T S.midpointTemp) := by
  have hWin := S.midpointTemp_mem_preformedPairWindow hCross
  exact ⟨hWin, preformedPairWindow_no_simple_or_fragmented_condensate hNorm hWin⟩

omit [DecidableEq κ] in
/-- Below `T_c`, a simply condensed occupation family is non-fragmented and possesses a
unique macroscopic occupation mode. -/
theorem belowTc_simple_not_fragmented
    {S : CrossoverScales} {F_of_T : ℝ → OccupationFamily κ} {T : ℝ}
    (hBelow : HasSimpleCondensationBelowTc S F_of_T)
    (hT : T < S.condensationTemp) :
    IsSimpleCondensate (F_of_T T) ∧
      ¬ IsFragmentedCondensate (F_of_T T) ∧
      ∀ i j, IsMacroscopicMode (F_of_T T) i → IsMacroscopicMode (F_of_T T) j → i = j := by
  have hS := hBelow T hT
  exact ⟨hS, simple_not_fragmented hS, fun _ _ hi hj => simple_macroscopic_mode_unique hS hi hj⟩

omit [DecidableEq κ] in
/-- Under strict BCS scale locking (`T^* = T_c`), simple condensation sets in immediately below
`T^*`, leaving no preformed-pair window. -/
theorem strictBCS_condenses_at_pairFormationTemp_boundary
    {S : CrossoverScales} {F_of_T : ℝ → OccupationFamily κ}
    (hBCS : S.IsStrictBCS) (hBelow : HasSimpleCondensationBelowTc S F_of_T) :
    (∀ T : ℝ, T < S.pairFormationTemp →
      IsSimpleCondensate (F_of_T T) ∧ ¬ IsFragmentedCondensate (F_of_T T)) ∧
      (∀ T : ℝ, ¬ S.InPreformedPairWindow T) := by
  refine ⟨fun T hT => ?_, fun T => S.strictBCS_preformedPairWindow_empty hBCS T⟩
  have hTc : T < S.condensationTemp := by
    unfold CrossoverScales.IsStrictBCS at hBCS
    linarith
  have hS := hBelow T hTc
  exact ⟨hS, simple_not_fragmented hS⟩

end BCSBECPhaseBridge

/-! ## BdG Quasiparticle Coherence & BCS/BEC Off-Diagonal Order Parameter -/

section BdGCoherenceBridge

open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Physics.NuclearBdGBogoliubovCAR
open InfoGeometry.Canonical.BCSBECScaleSeparation

/-- Coherent rank-one two-mode particle-hole kernel constructed from the normalized BdG
eigenmode `(uCoeff ξ Δ, vCoeff ξ Δ)`. -/
def bdgPairCoherenceKernel (ξ Δ : ℝ) : TwoModeKernel :=
  coherentTwoModeKernel (uCoeff ξ Δ : ℂ) (vCoeff ξ Δ : ℂ)

/-- Incoherent diagonal occupation kernel matching the diagonal entries of `bdgPairCoherenceKernel`. -/
def bdgIncoherentKernel (ξ Δ : ℝ) : TwoModeKernel :=
  incoherentKernelOfAmplitudes (uCoeff ξ Δ : ℂ) (vCoeff ξ Δ : ℂ)

/-- Exact BdG anomalous coherence identity: `u(ξ,Δ) * v(ξ,Δ) = Δ / (2 E(ξ,Δ))` for `Δ ≠ 0`. -/
theorem uCoeff_mul_vCoeff_eq_gap_over_two_energy
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    uCoeff ξ Δ * vCoeff ξ Δ = Δ / (2 * bdgEnergy ξ Δ) := by
  set E := bdgEnergy ξ Δ
  have hEsq : E ^ 2 = ξ ^ 2 + Δ ^ 2 := bdgEnergy_sq ξ Δ
  have hE_pos : 0 < E := Real.sqrt_pos.2 (by nlinarith [sq_pos_of_ne_zero hΔ, sq_nonneg ξ])
  have hExi_pos : 0 < E - ξ := by
    have hlt : ξ ^ 2 < E ^ 2 := by nlinarith [sq_pos_of_ne_zero hΔ]
    have habs : |ξ| < |E| := sq_lt_sq.mp hlt
    rw [abs_of_pos hE_pos] at habs
    linarith [le_abs_self ξ]
  have hraw : rawPositiveNormSq ξ Δ = 2 * E * (E - ξ) := by
    unfold rawPositiveNormSq
    change Δ ^ 2 + (E - ξ) ^ 2 = 2 * E * (E - ξ)
    nlinarith [hEsq]
  have hnorm_sq : positiveNorm ξ Δ ^ 2 = 2 * E * (E - ξ) := by
    rw [positiveNorm_sq hΔ, hraw]
  unfold uCoeff vCoeff
  calc
    (Δ / positiveNorm ξ Δ) * ((E - ξ) / positiveNorm ξ Δ)
        = (Δ * (E - ξ)) / (positiveNorm ξ Δ ^ 2) := by ring
    _ = (Δ * (E - ξ)) / (2 * E * (E - ξ)) := by rw [hnorm_sq]
    _ = Δ / (2 * E) := by
          have hE_ne : E ≠ 0 := ne_of_gt hE_pos
          have hExi_ne : E - ξ ≠ 0 := ne_of_gt hExi_pos
          field_simp [hE_ne, hExi_ne]

/-- Exact off-diagonal coherence amplitude `bdgPairCoherenceKernel ξ Δ 0 1 = Δ / (2 E(ξ,Δ)) ≠ 0`. -/
theorem bdgPairCoherenceKernel_offDiagonal
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    bdgPairCoherenceKernel ξ Δ 0 1 = ((Δ / (2 * bdgEnergy ξ Δ) : ℝ) : ℂ) ∧
      bdgPairCoherenceKernel ξ Δ 0 1 ≠ 0 := by
  have huv := uCoeff_mul_vCoeff_eq_gap_over_two_energy (ξ := ξ) (Δ := Δ) hΔ
  have h01 : bdgPairCoherenceKernel ξ Δ 0 1 = ((Δ / (2 * bdgEnergy ξ Δ) : ℝ) : ℂ) := by
    simp only [bdgPairCoherenceKernel, coherentTwoModeKernel_zero_one, Complex.conj_ofReal,
      ← Complex.ofReal_mul, huv]
  have hE_pos : 0 < bdgEnergy ξ Δ :=
    Real.sqrt_pos.2 (by nlinarith [sq_pos_of_ne_zero hΔ, sq_nonneg ξ])
  refine ⟨h01, ?_⟩
  rw [h01]
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero hΔ (mul_ne_zero (by norm_num) (ne_of_gt hE_pos)))

/-- For any nonzero pairing `Δ ≠ 0`, `bdgPairCoherenceKernel ξ Δ` is a rank-one idempotent
trace-1 density kernel strictly distinct from its diagonal incoherent counterpart `bdgIncoherentKernel`. -/
theorem bdgPairCoherenceKernel_trace_and_idempotent
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    Matrix.trace (bdgPairCoherenceKernel ξ Δ) = 1 ∧
      Matrix.det (bdgPairCoherenceKernel ξ Δ) = 0 ∧
      bdgPairCoherenceKernel ξ Δ * bdgPairCoherenceKernel ξ Δ = bdgPairCoherenceKernel ξ Δ ∧
      bdgPairCoherenceKernel ξ Δ 0 0 = bdgIncoherentKernel ξ Δ 0 0 ∧
      bdgPairCoherenceKernel ξ Δ 1 1 = bdgIncoherentKernel ξ Δ 1 1 ∧
      bdgPairCoherenceKernel ξ Δ ≠ bdgIncoherentKernel ξ Δ ∧
      Matrix.det (bdgIncoherentKernel ξ Δ) = (((Δ / (2 * bdgEnergy ξ Δ)) ^ 2 : ℝ) : ℂ) := by
  have huv1 : (uCoeff ξ Δ) ^ 2 + (vCoeff ξ Δ) ^ 2 = 1 := uCoeff_sq_add_vCoeff_sq hΔ
  have huv_prod := uCoeff_mul_vCoeff_eq_gap_over_two_energy (ξ := ξ) (Δ := Δ) hΔ
  have hcross : (uCoeff ξ Δ : ℂ) * starRingEnd ℂ (vCoeff ξ Δ : ℂ) ≠ 0 := by
    simpa [bdgPairCoherenceKernel] using (bdgPairCoherenceKernel_offDiagonal (ξ := ξ) (Δ := Δ) hΔ).2
  have htr : Matrix.trace (bdgPairCoherenceKernel ξ Δ) = 1 := by
    rw [bdgPairCoherenceKernel, coherentTwoModeKernel_trace]
    simp only [Complex.normSq_ofReal, ← sq, ← Complex.ofReal_add, huv1, Complex.ofReal_one]
  have hmode : modeNormSq (twoModeVector (uCoeff ξ Δ : ℂ) (vCoeff ξ Δ : ℂ)) = 1 := by
    simp [modeNormSq, twoModeVector, Fin.sum_univ_two, Complex.normSq_ofReal, ← sq, huv1]
  have hidem : bdgPairCoherenceKernel ξ Δ * bdgPairCoherenceKernel ξ Δ =
      bdgPairCoherenceKernel ξ Δ := by
    dsimp [bdgPairCoherenceKernel, coherentTwoModeKernel]
    rw [rankOneKernel_mul_rankOneKernel, hmode, Complex.ofReal_one, one_smul]
  have hdet_inc : Matrix.det (bdgIncoherentKernel ξ Δ) =
      (((Δ / (2 * bdgEnergy ξ Δ)) ^ 2 : ℝ) : ℂ) := by
    dsimp [bdgIncoherentKernel, incoherentKernelOfAmplitudes]
    rw [diagonalTwoModeKernel_det]
    simp only [Complex.normSq_ofReal, ← sq, ← Complex.ofReal_mul]
    congr 1
    calc (uCoeff ξ Δ ^ 2) * (vCoeff ξ Δ ^ 2)
        = (uCoeff ξ Δ * vCoeff ξ Δ) ^ 2 := by ring
      _ = (Δ / (2 * bdgEnergy ξ Δ)) ^ 2 := by rw [huv_prod]
  have hpacket := twoMode_coherence_packet hcross
  exact ⟨htr, hpacket.1, hidem, hpacket.2.2.2.1, hpacket.2.2.2.2.1, hpacket.2.2.2.2.2, hdet_inc⟩

/-- On the BCS side (`0 < μ`), the Fermi surface `ε = μ ≥ 0` attains maximal off-diagonal
pair coherence `|u v| = 1 / 2`. -/
theorem bcs_fermi_surface_maximal_pair_coherence
    {μ Δ : ℝ} (hμ : IsPositiveChemicalPotential μ) (hΔ : Δ ≠ 0) :
    ∃ ε : ℝ, 0 ≤ ε ∧ |uCoeff (ε - μ) Δ * vCoeff (ε - μ) Δ| = 1 / 2 := by
  refine ⟨μ, le_of_lt hμ, ?_⟩
  rw [sub_self, uCoeff_mul_vCoeff_eq_gap_over_two_energy hΔ]
  have hE : bdgEnergy 0 Δ = |Δ| := by simp [bdgEnergy, Real.sqrt_sq_eq_abs]
  rw [hE, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_abs]
  have hΔ_abs : |Δ| ≠ 0 := abs_ne_zero.mpr hΔ
  field_simp [hΔ_abs]

/-- On the BEC side (`μ < 0`), for every nonnegative kinetic energy `0 ≤ ε`, the anomalous
pair coherence `|u(ε - μ, Δ) * v(ε - μ, Δ)|` is bounded by `|Δ| / (2 bdgEnergy μ Δ) < 1 / 2`. -/
theorem bec_pair_coherence_suppressed
    {ε μ Δ : ℝ} (hμ : IsNegativeChemicalPotential μ) (hε : 0 ≤ ε) (hΔ : Δ ≠ 0) :
    |uCoeff (ε - μ) Δ * vCoeff (ε - μ) Δ| ≤ |Δ| / (2 * bdgEnergy μ Δ) ∧
      |Δ| / (2 * bdgEnergy μ Δ) < 1 / 2 := by
  rw [uCoeff_mul_vCoeff_eq_gap_over_two_energy hΔ]
  have hEμ_pos : 0 < bdgEnergy μ Δ :=
    Real.sqrt_pos.2 (by nlinarith [sq_pos_of_ne_zero hΔ, sq_nonneg μ])
  have hE_le : bdgEnergy μ Δ ≤ bdgEnergy (ε - μ) Δ :=
    bec_bdgEnergy_ge_zero_kinetic hμ hε Δ
  have hE_pos : 0 < bdgEnergy (ε - μ) Δ := lt_of_lt_of_le hEμ_pos hE_le
  have h1 : |Δ / (2 * bdgEnergy (ε - μ) Δ)| ≤ |Δ| / (2 * bdgEnergy μ Δ) := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hE_pos]
    exact div_le_div_of_nonneg_left (abs_nonneg Δ) (by linarith) (by linarith)
  have hgt := bec_min_gap_strictly_gt_abs_delta hμ Δ
  have h2 : |Δ| / (2 * bdgEnergy μ Δ) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    linarith
  exact ⟨h1, h2⟩

/-- Generalized BEC multi-mode off-diagonal coherence suppression across any nonempty finite
kinetic-energy shell `s : Finset κ` (`∀ k ∈ s, 0 ≤ ε k`):
1. Peak pair coherence `s.sup'` is bounded by `|Δ| / (2 bdgEnergy μ Δ) < 1 / 2`;
2. Total shell pair coherence `∑ k ∈ s, |u_k v_k|` is bounded above by
   `(s.card : ℝ) * (|Δ| / (2 bdgEnergy μ Δ))` and strictly below `(s.card : ℝ) / 2`;
3. Every mode kernel off-diagonal entry satisfies `‖bdgPairCoherenceKernel (ε k - μ) Δ 0 1‖ ≤ |Δ| / (2 bdgEnergy μ Δ)`. -/
theorem bec_spectrum_pair_coherence_suppressed
    {κ : Type*} (ε : κ → ℝ) (s : Finset κ) (hs : s.Nonempty)
    (hε : ∀ k ∈ s, 0 ≤ ε k)
    {μ Δ : ℝ} (hμ : IsNegativeChemicalPotential μ) (hΔ : Δ ≠ 0) :
    s.sup' hs (fun k => |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ|) ≤
        |Δ| / (2 * bdgEnergy μ Δ) ∧
      |Δ| / (2 * bdgEnergy μ Δ) < 1 / 2 ∧
      ∑ k ∈ s, |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ| ≤
        (s.card : ℝ) * (|Δ| / (2 * bdgEnergy μ Δ)) ∧
      ∑ k ∈ s, |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ| <
        (s.card : ℝ) / 2 ∧
      ∀ k ∈ s, ‖bdgPairCoherenceKernel (ε k - μ) Δ 0 1‖ ≤
        |Δ| / (2 * bdgEnergy μ Δ) := by
  have hpt : ∀ k ∈ s,
      |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ| ≤ |Δ| / (2 * bdgEnergy μ Δ) :=
    fun k hk => (bec_pair_coherence_suppressed hμ (hε k hk) hΔ).1
  have hlt : |Δ| / (2 * bdgEnergy μ Δ) < 1 / 2 := by
    rcases hs with ⟨k₀, hk₀⟩
    exact (bec_pair_coherence_suppressed hμ (hε k₀ hk₀) hΔ).2
  have hsup : s.sup' hs (fun k => |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ|) ≤
      |Δ| / (2 * bdgEnergy μ Δ) :=
    Finset.sup'_le hs _ hpt
  have hsum_le : ∑ k ∈ s, |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ| ≤
      (s.card : ℝ) * (|Δ| / (2 * bdgEnergy μ Δ)) := by
    calc ∑ k ∈ s, |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ|
        ≤ ∑ _k ∈ s, (|Δ| / (2 * bdgEnergy μ Δ)) := Finset.sum_le_sum hpt
      _ = (s.card : ℝ) * (|Δ| / (2 * bdgEnergy μ Δ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_pos : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
  have hsum_lt : ∑ k ∈ s, |uCoeff (ε k - μ) Δ * vCoeff (ε k - μ) Δ| < (s.card : ℝ) / 2 := by
    have hmul : (s.card : ℝ) * (|Δ| / (2 * bdgEnergy μ Δ)) < (s.card : ℝ) * (1 / 2) :=
      mul_lt_mul_of_pos_left hlt hcard_pos
    linarith
  refine ⟨hsup, hlt, hsum_le, hsum_lt, ?_⟩
  intro k hk
  have h01 := (bdgPairCoherenceKernel_offDiagonal (ξ := ε k - μ) (Δ := Δ) hΔ).1
  rw [h01, Complex.norm_real, Real.norm_eq_abs, ← uCoeff_mul_vCoeff_eq_gap_over_two_energy hΔ]
  exact hpt k hk

/-- At zero pairing (`Δ = 0`), the positive-energy BdG eigenmode collapses to a pure particle or
hole coordinate mode whose rank-one kernel coincides with the diagonal incoherent kernel. -/
theorem zero_pairing_coherence_collapse (ξ : ℝ) :
    ∃ a b : ℂ,
      a ^ 2 + b ^ 2 = 1 ∧
      Matrix.mulVec (bdgBlockC ξ 0) ![a, b] = (bdgEnergy ξ 0 : ℂ) • ![a, b] ∧
      coherentTwoModeKernel a b = incoherentKernelOfAmplitudes a b ∧
      coherentTwoModeKernel a b 0 1 = 0 := by
  by_cases hξ : 0 ≤ ξ
  · refine ⟨1, 0, by norm_num, ?_, ?_, by simp⟩
    · have hE : bdgEnergy ξ 0 = ξ := by
        rw [bdgEnergy_zero_pairing, abs_of_nonneg hξ]
      rw [hE]
      ext i
      fin_cases i <;> simp [bdgBlockC, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [incoherentKernelOfAmplitudes, diagonalTwoModeKernel]
  · have hξneg : ξ < 0 := lt_of_not_ge hξ
    refine ⟨0, 1, by norm_num, ?_, ?_, by simp⟩
    · have hE : bdgEnergy ξ 0 = -ξ := by
        rw [bdgEnergy_zero_pairing, abs_of_neg hξneg]
      rw [hE]
      ext i
      fin_cases i <;> simp [bdgBlockC, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [incoherentKernelOfAmplitudes, diagonalTwoModeKernel]

end BdGCoherenceBridge

/-! ## Explicit Simple Coherent vs. Fragmented Fock Occupation Families -/

section ExplicitOccupationFamilies

open Filter
open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Physics.NuclearBdGBogoliubovCAR

/-- Coherent two-mode condensate occupation family with total mode amplitude `(√N · a, √N · b)`:
the coherent mode `![a, b]` carries macroscopic occupation `N · (‖a‖² + ‖b‖²)`, while the
orthogonal mode carries occupation `0`. -/
def coherentPairCondensateFamily (a b : ℂ) : OccupationFamily (Fin 2) where
  occupation N i := match i with
    | 0 => (N : ℝ) * (Complex.normSq a + Complex.normSq b)
    | 1 => 0
  occupation_nonneg N i := by
    fin_cases i
    · exact mul_nonneg (Nat.cast_nonneg N)
        (add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b))
    · exact le_rfl

/-- Fragmented Fock two-mode occupation family corresponding to the incoherent diagonal kernel
`incoherentKernelOfAmplitudes (√N · a) (√N · b)` with macroscopic occupations `N · ‖a‖²` and `N · ‖b‖²`. -/
def fragmentedFockCondensateFamily (a b : ℂ) : OccupationFamily (Fin 2) where
  occupation N i := match i with
    | 0 => (N : ℝ) * Complex.normSq a
    | 1 => (N : ℝ) * Complex.normSq b
  occupation_nonneg N i := by
    fin_cases i
    · exact mul_nonneg (Nat.cast_nonneg N) (Complex.normSq_nonneg a)
    · exact mul_nonneg (Nat.cast_nonneg N) (Complex.normSq_nonneg b)

private lemma real_scaled_normSq (N : ℕ) (z : ℂ) :
    Complex.normSq ((Real.sqrt (N : ℝ) : ℂ) * z) = (N : ℝ) * Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg N)]

/-- The macroscopic occupation of `coherentPairCondensateFamily a b` equals the trace of the
population-scaled coherent rank-one kernel. -/
theorem coherentPairCondensateFamily_eq_trace (a b : ℂ) (N : ℕ) :
    ((coherentPairCondensateFamily a b).occupation N 0 : ℂ) =
      Matrix.trace (coherentTwoModeKernel ((Real.sqrt (N : ℝ) : ℂ) * a) ((Real.sqrt (N : ℝ) : ℂ) * b)) := by
  rw [coherentTwoModeKernel_trace, real_scaled_normSq, real_scaled_normSq]
  simp [coherentPairCondensateFamily, mul_add]

/-- The two occupations of `fragmentedFockCondensateFamily a b` equal the diagonal entries of the
population-scaled incoherent Fock kernel. -/
theorem fragmentedFockCondensateFamily_eq_diag (a b : ℂ) (N : ℕ) :
    ((fragmentedFockCondensateFamily a b).occupation N 0 : ℂ) =
        incoherentKernelOfAmplitudes ((Real.sqrt (N : ℝ) : ℂ) * a) ((Real.sqrt (N : ℝ) : ℂ) * b) 0 0 ∧
      ((fragmentedFockCondensateFamily a b).occupation N 1 : ℂ) =
        incoherentKernelOfAmplitudes ((Real.sqrt (N : ℝ) : ℂ) * a) ((Real.sqrt (N : ℝ) : ℂ) * b) 1 1 := by
  constructor
  · simp [fragmentedFockCondensateFamily, incoherentKernelOfAmplitudes, diagonalTwoModeKernel,
      real_scaled_normSq]
  · simp [fragmentedFockCondensateFamily, incoherentKernelOfAmplitudes, diagonalTwoModeKernel,
      real_scaled_normSq]

/-- Exact spectral decomposition of `coherentTwoModeKernel a b`: `twoModeVector a b` is the unique
eigenvector with eigenvalue `‖a‖² + ‖b‖²`, while `![-conj b, conj a]` lies in the kernel. -/
theorem coherentTwoModeKernel_eigen_spectrum (a b : ℂ) :
    (coherentTwoModeKernel a b).mulVec (twoModeVector a b) =
        ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) • twoModeVector a b ∧
      (coherentTwoModeKernel a b).mulVec ![-starRingEnd ℂ b, starRingEnd ℂ a] = 0 := by
  constructor
  · rw [funext_iff, Fin.forall_fin_two]
    constructor
    · simp only [coherentTwoModeKernel, rankOneKernel, twoModeVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul, Complex.mul_conj]
      rw [mul_assoc a (starRingEnd ℂ b) b, mul_comm (starRingEnd ℂ b) b, Complex.mul_conj]
      push_cast; ring
    · simp only [coherentTwoModeKernel, rankOneKernel, twoModeVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul, Complex.mul_conj]
      rw [mul_assoc b (starRingEnd ℂ a) a, mul_comm (starRingEnd ℂ a) a, Complex.mul_conj]
      push_cast; ring
  · ext i
    fin_cases i <;>
      simp [coherentTwoModeKernel, rankOneKernel, twoModeVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> ring

private lemma not_macroscopic_zero (F : OccupationFamily (Fin 2)) (i : Fin 2)
    (h0 : ∀ N, F.occupation N i = 0) : ¬ IsMacroscopicMode F i := by
  rintro ⟨c, hc, hEv⟩
  rcases Filter.eventually_atTop.mp hEv with ⟨N₀, hN₀⟩
  have hle := hN₀ N₀ (le_refl N₀)
  simp [scaledOccupation, h0] at hle
  linarith

/-- Whenever `(a, b) ≠ (0, 0)`, the coherent pair family is a **simple condensate**
(and therefore not fragmented). -/
theorem coherentPairCondensateFamily_isSimple {a b : ℂ} (hab : a ≠ 0 ∨ b ≠ 0) :
    IsSimpleCondensate (coherentPairCondensateFamily a b) ∧
      ¬ IsFragmentedCondensate (coherentPairCondensateFamily a b) := by
  have hc_pos : 0 < Complex.normSq a + Complex.normSq b := by
    rcases hab with ha | hb
    · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr ha) (Complex.normSq_nonneg b)
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg a) (Complex.normSq_pos.mpr hb)
  have hm0 : IsMacroscopicMode (coherentPairCondensateFamily a b) 0 := by
    refine ⟨Complex.normSq a + Complex.normSq b, hc_pos, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
    simp only [scaledOccupation, coherentPairCondensateFamily, populationScale]
    have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
    rw [mul_div_cancel_left₀ _ hpos.ne']
  have hnot1 : ¬ IsMacroscopicMode (coherentPairCondensateFamily a b) 1 :=
    not_macroscopic_zero _ 1 (fun _ => rfl)
  have hSimple : IsSimpleCondensate (coherentPairCondensateFamily a b) := by
    refine ⟨0, hm0, fun j hj => ?_⟩
    fin_cases j
    · rfl
    · exact (hnot1 hj).elim
  exact ⟨hSimple, simple_not_fragmented hSimple⟩

/-- Whenever `a ≠ 0` and `b ≠ 0`, the incoherent Fock diagonal family is a **fragmented condensate**
(and therefore not simple). -/
theorem fragmentedFockCondensateFamily_isFragmented {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsFragmentedCondensate (fragmentedFockCondensateFamily a b) ∧
      ¬ IsSimpleCondensate (fragmentedFockCondensateFamily a b) := by
  have hm0 : IsMacroscopicMode (fragmentedFockCondensateFamily a b) 0 := by
    refine ⟨Complex.normSq a, Complex.normSq_pos.mpr ha, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
    simp only [scaledOccupation, fragmentedFockCondensateFamily, populationScale]
    have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
    rw [mul_div_cancel_left₀ _ hpos.ne']
  have hm1 : IsMacroscopicMode (fragmentedFockCondensateFamily a b) 1 := by
    refine ⟨Complex.normSq b, Complex.normSq_pos.mpr hb, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
    simp only [scaledOccupation, fragmentedFockCondensateFamily, populationScale]
    have hpos : (0 : ℝ) < (n.succ : ℝ) := by positivity
    rw [mul_div_cancel_left₀ _ hpos.ne']
  have hFrag : IsFragmentedCondensate (fragmentedFockCondensateFamily a b) :=
    ⟨0, 1, by decide, hm0, hm1⟩
  exact ⟨hFrag, fun hSimple => simple_not_fragmented hSimple hFrag⟩

/-- **Direct Bridge: Coherent Rank-One (`IsSimpleCondensate`) vs. Incoherent Fock (`IsFragmentedCondensate`)**:
For any nonzero cross-coherence `a * conj b ≠ 0`, the population-scaled coherent and incoherent
kernels share identical diagonal occupations and trace at every scale `N ≥ 1`, yet differ
off-diagonally (`det K_coh = 0` vs `det K_inc ≠ 0`), separating `IsSimpleCondensate` from
`IsFragmentedCondensate`. -/
theorem coherentTwoMode_simple_vs_incoherent_fragmented_bridge
    {a b : ℂ} (hab : a * starRingEnd ℂ b ≠ 0) :
    (IsSimpleCondensate (coherentPairCondensateFamily a b) ∧
      ¬ IsFragmentedCondensate (coherentPairCondensateFamily a b)) ∧
    (IsFragmentedCondensate (fragmentedFockCondensateFamily a b) ∧
      ¬ IsSimpleCondensate (fragmentedFockCondensateFamily a b)) ∧
    (∀ N : ℕ, 0 < N →
      let aN : ℂ := (Real.sqrt (N : ℝ) : ℂ) * a
      let bN : ℂ := (Real.sqrt (N : ℝ) : ℂ) * b
      coherentTwoModeKernel aN bN 0 0 = incoherentKernelOfAmplitudes aN bN 0 0 ∧
      coherentTwoModeKernel aN bN 1 1 = incoherentKernelOfAmplitudes aN bN 1 1 ∧
      Matrix.trace (coherentTwoModeKernel aN bN) =
        Matrix.trace (incoherentKernelOfAmplitudes aN bN) ∧
      coherentTwoModeKernel aN bN ≠ incoherentKernelOfAmplitudes aN bN ∧
      Matrix.det (coherentTwoModeKernel aN bN) = 0 ∧
      Matrix.det (incoherentKernelOfAmplitudes aN bN) ≠ 0 ∧
      (coherentTwoModeKernel aN bN).mulVec (twoModeVector a b) =
        (((N : ℝ) * (Complex.normSq a + Complex.normSq b) : ℝ) : ℂ) • twoModeVector a b) := by
  have ha : a ≠ 0 := fun h0 => hab (by simp [h0])
  have hb : b ≠ 0 := fun h0 => hab (by simp [h0])
  refine ⟨coherentPairCondensateFamily_isSimple (Or.inl ha),
    fragmentedFockCondensateFamily_isFragmented ha hb, ?_⟩
  intro N hN aN bN
  have habN : aN * starRingEnd ℂ bN ≠ 0 := by
    dsimp [aN, bN]
    have hsqrt : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN))
    simp only [map_mul]
    intro hzero
    have hmul : (Real.sqrt (N : ℝ) : ℂ) * starRingEnd ℂ (Real.sqrt (N : ℝ) : ℂ) *
        (a * starRingEnd ℂ b) = 0 := by
      linear_combination hzero
    rcases mul_eq_zero.mp hmul with h1 | h2
    · rcases mul_eq_zero.mp h1 with hc | hc
      · exact hsqrt hc
      · exact hsqrt ((starRingEnd ℂ).injective (by simpa using hc))
    · exact hab h2
  have hPkt := twoMode_coherence_packet habN
  have hDetInc : Matrix.det (incoherentKernelOfAmplitudes aN bN) ≠ 0 := by
    unfold incoherentKernelOfAmplitudes
    rw [diagonalTwoModeKernel_det]
    have hna : (Complex.normSq aN : ℂ) ≠ 0 := by
      have haN : aN ≠ 0 := fun h0 => habN (by simp [h0])
      exact Complex.ofReal_ne_zero.mpr (Complex.normSq_pos.mpr haN).ne'
    have hnb : (Complex.normSq bN : ℂ) ≠ 0 := by
      have hbN : bN ≠ 0 := fun h0 => habN (by simp [h0])
      exact Complex.ofReal_ne_zero.mpr (Complex.normSq_pos.mpr hbN).ne'
    exact mul_ne_zero hna hnb
  have hEig : (coherentTwoModeKernel aN bN).mulVec (twoModeVector a b) =
      (((N : ℝ) * (Complex.normSq a + Complex.normSq b) : ℝ) : ℂ) • twoModeVector a b := by
    have hsq : (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N), Complex.ofReal_natCast]
    rw [funext_iff, Fin.forall_fin_two]
    constructor
    · simp only [coherentTwoModeKernel, rankOneKernel, twoModeVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul, aN, bN, map_mul, Complex.conj_ofReal]
      calc
        (Real.sqrt (N : ℝ) : ℂ) * a * ((Real.sqrt (N : ℝ) : ℂ) * starRingEnd ℂ a) * a +
            (Real.sqrt (N : ℝ) : ℂ) * a * ((Real.sqrt (N : ℝ) : ℂ) * starRingEnd ℂ b) * b
          = ((Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ)) *
              ((a * starRingEnd ℂ a + b * starRingEnd ℂ b) * a) := by ring
        _ = (N : ℂ) * ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) * a := by
            rw [hsq, Complex.mul_conj, Complex.mul_conj]; push_cast; ring
        _ = (((N : ℝ) * (Complex.normSq a + Complex.normSq b) : ℝ) : ℂ) * a := by
            push_cast; ring
    · simp only [coherentTwoModeKernel, rankOneKernel, twoModeVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul, aN, bN, map_mul, Complex.conj_ofReal]
      calc
        (Real.sqrt (N : ℝ) : ℂ) * b * ((Real.sqrt (N : ℝ) : ℂ) * starRingEnd ℂ a) * a +
            (Real.sqrt (N : ℝ) : ℂ) * b * ((Real.sqrt (N : ℝ) : ℂ) * starRingEnd ℂ b) * b
          = ((Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ)) *
              ((a * starRingEnd ℂ a + b * starRingEnd ℂ b) * b) := by ring
        _ = (N : ℂ) * ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) * b := by
            rw [hsq, Complex.mul_conj, Complex.mul_conj]; push_cast; ring
        _ = (((N : ℝ) * (Complex.normSq a + Complex.normSq b) : ℝ) : ℂ) * b := by
            push_cast; ring
  refine ⟨hPkt.2.2.2.1, hPkt.2.2.2.2.1, ?_, hPkt.2.2.2.2.2, hPkt.1, hDetInc, hEig⟩
  rw [coherentTwoModeKernel_trace]
  unfold incoherentKernelOfAmplitudes
  rw [diagonalTwoModeKernel_trace]

/-- **Coherent Two-Sheeted BdG Pair Condensate Realization**:
For any kinetic detuning `ξ` and nonzero pairing gap `Δ ≠ 0`, the Bogoliubov eigenmode
`(uCoeff ξ Δ, vCoeff ξ Δ)` yields:
1. A simple coherent condensate `IsSimpleCondensate (coherentPairCondensateFamily u v)` with
   macroscopic occupation `N` in the single coherent pair mode,
2. A fragmented incoherent Fock condensate `IsFragmentedCondensate (fragmentedFockCondensateFamily u v)`
   when `u` and `v` are incoherently superposed (`bdgIncoherentKernel ξ Δ`). -/
theorem bdg_coherent_pair_condensate_simple_vs_fragmented
    {ξ Δ : ℝ} (hΔ : Δ ≠ 0) :
    let u : ℂ := (uCoeff ξ Δ : ℂ)
    let v : ℂ := (vCoeff ξ Δ : ℂ)
    IsNormalizedMode (twoModeVector u v) ∧
    u * starRingEnd ℂ v ≠ 0 ∧
    IsSimpleCondensate (coherentPairCondensateFamily u v) ∧
    ¬ IsFragmentedCondensate (coherentPairCondensateFamily u v) ∧
    IsFragmentedCondensate (fragmentedFockCondensateFamily u v) ∧
    ¬ IsSimpleCondensate (fragmentedFockCondensateFamily u v) := by
  intro u v
  have huv1 : (uCoeff ξ Δ) ^ 2 + (vCoeff ξ Δ) ^ 2 = 1 := uCoeff_sq_add_vCoeff_sq hΔ
  have hmode : IsNormalizedMode (twoModeVector u v) := by
    simp [IsNormalizedMode, modeNormSq, twoModeVector, Fin.sum_univ_two,
      Complex.normSq_ofReal, ← sq, huv1, u, v]
  have hcross : u * starRingEnd ℂ v ≠ 0 := by
    simpa [bdgPairCoherenceKernel, u, v] using
      (bdgPairCoherenceKernel_offDiagonal (ξ := ξ) (Δ := Δ) hΔ).2
  have hBridge := coherentTwoMode_simple_vs_incoherent_fragmented_bridge hcross
  exact ⟨hmode, hcross, hBridge.1.1, hBridge.1.2, hBridge.2.1.1, hBridge.2.1.2⟩

end ExplicitOccupationFamilies

end InfoGeometry.Canonical.PenroseOnsagerYangCondensationPristineChain

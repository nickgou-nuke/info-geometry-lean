/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.KMSStripKleinMonodromy
import InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget
import InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
import InfoGeometry.Canonical.CantorBoundaryFiniteReadout
import InfoGeometry.Canonical.CantorBoundaryDyadicCover
import InfoGeometry.Canonical.WheelerItFromBit
import InfoGeometry.Probability.DetectorTrueCoincidenceSumming
import InfoGeometry.Probability.SymmetricCounting
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# KMS logistic coordinate and the Cantor binary-readout quotient

The binary Cantor readout quotient is homeomorphic to the closed unit interval.
This file transports the existing KMS logistic coordinate into that quotient
and identifies time reversal with reflection of the readout coordinate.
It does not select a binary expansion at dyadic points or identify the readout
with the separate finite-spinor Wheeler observable.
-/

noncomputable section

namespace InfoGeometry.Canonical.KMSCantorLogisticBridge

open InfoGeometry.NCG.KMSStripKleinMonodromy
open InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget
open InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat
open InfoGeometry.Canonical.CantorBoundaryComplexReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryDyadicCover
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.WheelerItFromBit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Physics.EmergentSpacetimeBilinear
open InfoGeometry.Probability.DetectorTrueCoincidenceSumming

/-- Reflection of the closed unit interval. -/
def readoutIntervalComplement (x : UnitInterval) : UnitInterval :=
  ⟨1 - x.1, ⟨by linarith [x.2.2], by linarith [x.2.1]⟩⟩

/-- Reflection of the Cantor readout quotient induced by `x ↦ 1 - x` on
the unit interval. -/
def readoutComplement (q : ReadoutQuotient) : ReadoutQuotient :=
  canonicalQuotientReadoutIntervalHomeomorph.symm
    (readoutIntervalComplement
      (canonicalQuotientReadoutIntervalHomeomorph q))

/-- The logistic coordinate as a point of the unit interval. -/
def kmsUnitInterval (t : ℝ) : UnitInterval :=
  ⟨compactifiedTime t,
    ⟨(compactifiedTime_mem_unitInterval t).1.le,
     (compactifiedTime_mem_unitInterval t).2.le⟩⟩

/-- The KMS logistic coordinate, regarded as a point of the canonical
Cantor-readout quotient. -/
def kmsCantorReadout (t : ℝ) : ReadoutQuotient :=
  canonicalQuotientReadoutIntervalHomeomorph.symm
    (kmsUnitInterval t)

/-- The quotient readout of the transported KMS coordinate is exactly its
logistic compactification value. -/
theorem quotientReadout_kmsCantorReadout (t : ℝ) :
    quotientReadoutInterval (kmsCantorReadout t) = kmsUnitInterval t := by
  exact canonicalQuotientReadoutIntervalHomeomorph.apply_symm_apply _

/-- The Klein time reflection `t ↦ -t` acts on the Cantor-readout quotient
through the complementary coordinate `x ↦ 1 - x`. -/
theorem kmsCantorReadout_timeReflection (t : ℝ) :
    kmsCantorReadout (-t) = readoutComplement (kmsCantorReadout t) := by
  apply canonicalQuotientReadoutIntervalHomeomorph.injective
  change canonicalQuotientReadoutIntervalHomeomorph
      (canonicalQuotientReadoutIntervalHomeomorph.symm (kmsUnitInterval (-t))) =
    canonicalQuotientReadoutIntervalHomeomorph
      (canonicalQuotientReadoutIntervalHomeomorph.symm
        (readoutIntervalComplement
          (canonicalQuotientReadoutIntervalHomeomorph
            (canonicalQuotientReadoutIntervalHomeomorph.symm (kmsUnitInterval t)))))
  simp only [canonicalQuotientReadoutIntervalHomeomorph.apply_symm_apply]
  apply Subtype.ext
  exact compactifiedTime_neg t

/-- The induced readout reflection is an involution on the quotient. -/
theorem readoutComplement_involutive (q : ReadoutQuotient) :
    readoutComplement (readoutComplement q) = q := by
  apply canonicalQuotientReadoutIntervalHomeomorph.injective
  change canonicalQuotientReadoutIntervalHomeomorph
      (canonicalQuotientReadoutIntervalHomeomorph.symm
        (readoutIntervalComplement
          (canonicalQuotientReadoutIntervalHomeomorph
            (canonicalQuotientReadoutIntervalHomeomorph.symm
              (readoutIntervalComplement
                (canonicalQuotientReadoutIntervalHomeomorph q)))))) = _
  simp only [canonicalQuotientReadoutIntervalHomeomorph.apply_symm_apply]
  apply Subtype.ext
  simp [readoutIntervalComplement]

/-- Complementing every Cantor bit complements its real binary readout. -/
theorem realBinaryReadout_complement (w : ℕ → Bool) :
    realBinaryReadout (fun n => !w n) + realBinaryReadout w = 1 := by
  have h := binary_readout_complement w
  rw [complex_binaryReadout_eq_ofReal, complex_binaryReadout_eq_ofReal] at h
  have hre := congrArg Complex.re h
  simpa using hre

/-- The interval readout of a quotient class is its binary-stream readout. -/
theorem quotientReadoutInterval_quotientMap (w : ℕ → Bool) :
    quotientReadoutInterval (quotientMap w) =
      ⟨realBinaryReadout w, realBinaryReadout_mem_unitInterval w⟩ := by
  apply Subtype.ext
  exact quotientReadout_comp w

/-- The interval reflection on the readout quotient is induced by the
pointwise complement of a Cantor stream. -/
theorem readoutComplement_quotientMap (w : ℕ → Bool) :
    readoutComplement (quotientMap w) = quotientMap (fun n => !w n) := by
  apply canonicalQuotientReadoutIntervalHomeomorph.injective
  change canonicalQuotientReadoutIntervalHomeomorph
      (canonicalQuotientReadoutIntervalHomeomorph.symm
        (readoutIntervalComplement
          (canonicalQuotientReadoutIntervalHomeomorph (quotientMap w)))) =
    canonicalQuotientReadoutIntervalHomeomorph
      (quotientMap (fun n => !w n))
  rw [canonicalQuotientReadoutIntervalHomeomorph.apply_symm_apply]
  simp only [canonicalQuotientReadoutIntervalHomeomorph_apply]
  rw [quotientReadoutInterval_quotientMap, quotientReadoutInterval_quotientMap]
  apply Subtype.ext
  change 1 - realBinaryReadout w = realBinaryReadout (fun n => !w n)
  have h := realBinaryReadout_complement w
  linarith

/-- A finite Wheeler spinor/operator readout transported to the Cantor
readout quotient through the KMS logistic coordinate. -/
def wheelerCantorReadout
    (psi : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (A : InfoGeometry.Canonical.WheelerItFromBit.Mat32) : ReadoutQuotient :=
  kmsCantorReadout (itFromBitCoordinate psi A)

/-- Operator sign reversal in the Wheeler trace readout is transported to
Cantor bit-complement reflection. -/
theorem wheelerCantorReadout_neg
    (psi : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (A : InfoGeometry.Canonical.WheelerItFromBit.Mat32) :
    wheelerCantorReadout psi (-A) = readoutComplement (wheelerCantorReadout psi A) := by
  have hreadout : itFromBitCoordinate psi (-A) = -itFromBitCoordinate psi A := by
    simp [itFromBitCoordinate, spacetimeCoordinate]
  unfold wheelerCantorReadout
  rw [hreadout]
  exact kmsCantorReadout_timeReflection (itFromBitCoordinate psi A)

/-- The zero-spinor Wheeler readout lies at the logistic midpoint of the
Cantor quotient. -/
theorem wheelerZeroState_midpoint
    (A : InfoGeometry.Canonical.WheelerItFromBit.Mat32) :
    quotientReadoutInterval (wheelerCantorReadout 0 A) = kmsUnitInterval 0 := by
  rw [wheelerCantorReadout, it_vanishes_for_zero_state,
    quotientReadout_kmsCantorReadout]

/-- The logistic compactification of every finite-spinor Wheeler coordinate
lies in a dyadic interval selected by an actual length-`N` bitword. Its width
is the canonical finite-prefix error `(1/2)^N`. -/
theorem wheeler_logistic_finite_bitword_cover
    (psi : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (A : InfoGeometry.Canonical.WheelerItFromBit.Mat32) (N : ℕ) :
    ∃ w : BitWord N,
      |compactifiedTime (itFromBitCoordinate psi A) -
        finitePrefixReadout (List.ofFn w)| ≤ (1 / 2 : ℝ) ^ N := by
  obtain ⟨w, hw⟩ := exists_prefix_dyadic_cover
    (compactifiedTime (itFromBitCoordinate psi A))
    ⟨by linarith [compactifiedTime_mem_unitInterval (itFromBitCoordinate psi A)],
     by linarith [compactifiedTime_mem_unitInterval (itFromBitCoordinate psi A)]⟩ N
  refine ⟨w, ?_⟩
  rw [abs_of_nonneg (by linarith [hw.1])]
  linarith [hw.2]

/-- The real log-odds coordinate is inverse to the logistic compactification
on the open unit interval. -/
def logOddsCoordinate (p : ℝ) : ℝ := Real.log (p / (1 - p))

theorem compactifiedTime_logOddsCoordinate {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    compactifiedTime (logOddsCoordinate p) = p := by
  have hratio : 0 < p / (1 - p) := div_pos hp (by linarith)
  have hden : 1 - p ≠ 0 := ne_of_gt (by linarith)
  unfold compactifiedTime logOddsCoordinate
  rw [Real.exp_log hratio]
  field_simp [hden]
  ring_nf

/-- Complementing a unit-interval coordinate inverts its odds and negates
the corresponding log-odds coordinate. -/
theorem logOddsCoordinate_one_sub {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    logOddsCoordinate (1 - p) = -logOddsCoordinate p := by
  unfold logOddsCoordinate
  have h1p : 0 < 1 - p := by linarith
  have hden : 1 - (1 - p) = p := by ring
  rw [hden]
  rw [Real.log_div (ne_of_gt h1p) (ne_of_gt hp),
    Real.log_div (ne_of_gt hp) (ne_of_gt h1p)]
  ring

/-- Every open-unit-interval detector ratio has a canonical point in the
Cantor readout quotient whose coordinate is that ratio. -/
theorem quotientReadout_logOddsCoordinate {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    quotientReadoutInterval (kmsCantorReadout (logOddsCoordinate p)) =
      ⟨p, ⟨hp.le, hp1.le⟩⟩ := by
  rw [quotientReadout_kmsCantorReadout]
  apply Subtype.ext
  exact compactifiedTime_logOddsCoordinate hp hp1

/-! ## Finite Peirce operator readout into the Cantor bit address -/

/-- The finite Wheeler trace readout of the Peirce logistic operator on the
native `32 × 32` real spinor carrier. This is an observable map: it does not
identify the operator itself with a scalar logistic coordinate. -/
def peirceWheelerCantorReadout
    (psi : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (P A C : InfoGeometry.Canonical.WheelerItFromBit.Mat32) : ReadoutQuotient :=
  wheelerCantorReadout psi (peirceLogisticPlus P A C)

/-- The Cantor quotient coordinate of a Peirce operator is exactly the
analytic logistic compactification of its finite Wheeler trace readout. -/
theorem peirceWheelerCantorReadout_coordinate
    (psi : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (P A C : InfoGeometry.Canonical.WheelerItFromBit.Mat32) :
    quotientReadoutInterval (peirceWheelerCantorReadout psi P A C) =
      kmsUnitInterval (spacetimeCoordinate psi (peirceLogisticPlus P A C)) := by
  unfold peirceWheelerCantorReadout wheelerCantorReadout itFromBitCoordinate
  exact quotientReadout_kmsCantorReadout _

/-- The compactified Wheeler readout of every Peirce logistic operator lies
in a finite Cantor bitword cylinder at every resolution. -/
theorem peirceWheelerCantorReadout_finite_bitword
    (psi : InfoGeometry.Canonical.WheelerItFromBit.Spinor32)
    (P A C : InfoGeometry.Canonical.WheelerItFromBit.Mat32)
    (N : ℕ) :
    ∃ w : BitWord N,
      compactifiedTime (spacetimeCoordinate psi (peirceLogisticPlus P A C)) ∈
        Set.Icc (finitePrefixReadout (List.ofFn w))
          (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ N) := by
  let t := spacetimeCoordinate psi (peirceLogisticPlus P A C)
  have hcompact : compactifiedTime t ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨(compactifiedTime_mem_unitInterval t).1.le,
      (compactifiedTime_mem_unitInterval t).2.le⟩
  exact exists_prefix_dyadic_cover (compactifiedTime t) hcompact N

/-- The existing gamma-2 coincidence slope extraction is carried by the
log-odds chart to the Cantor quotient. -/
theorem coincidenceGamma2_cantorReadout
    (A f1 f2 gp1 gp2 gt2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0)
    (hgp1 : gp1 ≠ 0) (hW : W ≠ 0)
    (hgp2 : 0 < gp2) (hgp2gt2 : gp2 < gt2) :
    quotientReadoutInterval
      (kmsCantorReadout
        (logOddsCoordinate
          (sumPeakSlope A f1 f2 gp1 gp2 W /
            lossSlope A f1 f2 gp1 gt2 W))) =
      ⟨peakToTotal gp2 gt2,
        ⟨(div_pos hgp2 (by linarith)).le,
         ((div_lt_one (by linarith)).2 hgp2gt2).le⟩⟩ := by
  have hgt2 : gt2 ≠ 0 := ne_of_gt (lt_trans hgp2 hgp2gt2)
  have hratio := peakToTotal_extraction_gamma2
    A f1 f2 gp1 gp2 gt2 W hA hf1 hf2 hgp1 hgt2 hW
  rw [hratio]
  exact quotientReadout_logOddsCoordinate
    (div_pos hgp2 (by linarith)) ((div_lt_one (by linarith)).2 hgp2gt2)

/-- The gamma-2 coincidence extraction has a finite Cantor-cylinder
approximation: at every depth `N`, the measured sum-peak/loss slope ratio lies
in a dyadic interval indexed by an actual length-`N` bitword. -/
theorem coincidenceGamma2_finite_bitword_cover
    (A f1 f2 gp1 gp2 gt2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0)
    (hgp1 : gp1 ≠ 0) (hW : W ≠ 0)
    (hgp2 : 0 < gp2) (hgp2gt2 : gp2 < gt2) (N : ℕ) :
    ∃ w : BitWord N,
      sumPeakSlope A f1 f2 gp1 gp2 W /
        lossSlope A f1 f2 gp1 gt2 W ∈ Set.Icc
          (finitePrefixReadout (List.ofFn w))
          (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ N) := by
  have hgt2 : gt2 ≠ 0 := ne_of_gt (lt_trans hgp2 hgp2gt2)
  have hgt2pos : 0 < gt2 := lt_trans hgp2 hgp2gt2
  have hextract := peakToTotal_extraction_gamma2
    A f1 f2 gp1 gp2 gt2 W hA hf1 hf2 hgp1 hgt2 hW
  have hratio_pos : 0 < peakToTotal gp2 gt2 := div_pos hgp2 hgt2pos
  have hratio_lt_one : peakToTotal gp2 gt2 < 1 :=
    (div_lt_one hgt2pos).2 hgp2gt2
  obtain ⟨w, hw⟩ := exists_prefix_dyadic_cover (peakToTotal gp2 gt2)
    ⟨hratio_pos.le, hratio_lt_one.le⟩ N
  refine ⟨w, ?_⟩
  rw [hextract]
  exact hw

/-- At every positive integer resolution `n`, the exact gamma-2
peak-to-total ratio determines a natural coincidence count by flooring
`n * peakToTotal`. The normalized count is below the measured ratio and
within `1 / n`; under the stated interior and resolution bounds, the count is
strictly between zero and `n`. This is the finite arithmetic discretization
of the extracted ratio, not a stochastic model of detector events. -/
theorem coincidenceGamma2_finite_count_resolution
    (A f1 f2 gp1 gp2 gt2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0)
    (hgp1 : gp1 ≠ 0) (hW : W ≠ 0)
    (hgp2 : 0 < gp2) (hgp2gt2 : gp2 < gt2)
    (n : ℕ) (hn : 0 < n)
    (hresolution : 1 ≤ (n : ℝ) * peakToTotal gp2 gt2) :
    let coincidenceCount := ⌊(n : ℝ) * peakToTotal gp2 gt2⌋₊
    0 < coincidenceCount ∧ coincidenceCount < n ∧
      (coincidenceCount : ℝ) / n ≤
        sumPeakSlope A f1 f2 gp1 gp2 W / lossSlope A f1 f2 gp1 gt2 W ∧
      sumPeakSlope A f1 f2 gp1 gp2 W / lossSlope A f1 f2 gp1 gt2 W <
        (coincidenceCount : ℝ) / n + 1 / n := by
  dsimp
  have hgt2 : gt2 ≠ 0 := ne_of_gt (lt_trans hgp2 hgp2gt2)
  have hgt2pos : 0 < gt2 := lt_trans hgp2 hgp2gt2
  have hextract := peakToTotal_extraction_gamma2
    A f1 f2 gp1 gp2 gt2 W hA hf1 hf2 hgp1 hgt2 hW
  have hpPos : 0 < peakToTotal gp2 gt2 := div_pos hgp2 hgt2pos
  have hpLt : peakToTotal gp2 gt2 < 1 :=
    (div_lt_one hgt2pos).2 hgp2gt2
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnpNonneg : 0 ≤ (n : ℝ) * peakToTotal gp2 gt2 :=
    mul_nonneg hnPos.le hpPos.le
  have hcountPos : 0 < ⌊(n : ℝ) * peakToTotal gp2 gt2⌋₊ := by
    exact Nat.floor_pos.mpr hresolution
  have hcountLt : ⌊(n : ℝ) * peakToTotal gp2 gt2⌋₊ < n := by
    apply (Nat.floor_lt hnpNonneg).mpr
    nlinarith
  have hfloorLe :
      (⌊(n : ℝ) * peakToTotal gp2 gt2⌋₊ : ℝ) ≤
        (n : ℝ) * peakToTotal gp2 gt2 := Nat.floor_le hnpNonneg
  have hltFloorAddOne :
      (n : ℝ) * peakToTotal gp2 gt2 <
        (⌊(n : ℝ) * peakToTotal gp2 gt2⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨hcountPos, hcountLt, ?_, ?_⟩
  · rw [hextract]
    apply (div_le_iff₀ hnPos).2
    nlinarith
  · rw [hextract]
    rw [← add_div]
    apply (lt_div_iff₀ hnPos).2
    nlinarith

/-- A finite coincidence count normalized by the total number of trials has
both a logistic Cantor-quotient coordinate and a finite dyadic bitword
approximation. This theorem keeps the discrete event count explicit; it does
not identify that count with the real-valued detector slope model. -/
theorem finite_coincidence_count_logistic_bitword_bridge
    (coincidenceCount totalCount : ℕ)
    (hcount : 0 < coincidenceCount) (hcount_total : coincidenceCount < totalCount)
    (N : ℕ) :
    quotientReadoutInterval
        (kmsCantorReadout
          (logOddsCoordinate ((coincidenceCount : ℝ) / (totalCount : ℝ)))) =
      ⟨(coincidenceCount : ℝ) / (totalCount : ℝ),
        ⟨(div_pos (by exact_mod_cast hcount)
            (by exact_mod_cast (lt_trans hcount hcount_total))).le,
         ((div_lt_one (by exact_mod_cast (lt_trans hcount hcount_total))).2
           (by exact_mod_cast hcount_total)).le⟩⟩ ∧
    ∃ w : BitWord N,
      (coincidenceCount : ℝ) / (totalCount : ℝ) ∈
        Set.Icc (finitePrefixReadout (List.ofFn w))
          (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ N) := by
  have htotal : 0 < (totalCount : ℝ) := by
    exact_mod_cast (lt_trans hcount hcount_total)
  have hcountR : 0 < (coincidenceCount : ℝ) := by exact_mod_cast hcount
  have hcountLt : (coincidenceCount : ℝ) < (totalCount : ℝ) := by
    exact_mod_cast hcount_total
  have hratio : 0 < (coincidenceCount : ℝ) / (totalCount : ℝ) :=
    div_pos hcountR htotal
  have hratio_lt_one :
      (coincidenceCount : ℝ) / (totalCount : ℝ) < 1 :=
    (div_lt_one htotal).2 hcountLt
  refine ⟨quotientReadout_logOddsCoordinate hratio hratio_lt_one, ?_⟩
  obtain ⟨w, hw⟩ := exists_prefix_dyadic_cover
    ((coincidenceCount : ℝ) / (totalCount : ℝ))
    ⟨hratio.le, hratio_lt_one.le⟩ N
  exact ⟨w, hw⟩

/-- A finite coincidence event set, as a nonempty proper subset of a finite
trial set, has a normalized cardinality whose log-odds coordinate lies in the
Cantor readout quotient and whose empirical frequency has finite bitword
approximations. This uses actual finite-set cardinalities rather than an
abstract pair of natural counts. -/
theorem finite_coincidence_event_set_logistic_bitword_bridge
    {α : Type*} [DecidableEq α]
    (trials coincidences : Finset α)
    (hsubset : coincidences ⊆ trials)
    (hne : coincidences.Nonempty)
    (hproper : coincidences ≠ trials)
    (N : ℕ) :
    (quotientReadoutInterval
        (kmsCantorReadout
          (logOddsCoordinate ((coincidences.card : ℝ) / (trials.card : ℝ))))).1 =
      (coincidences.card : ℝ) / (trials.card : ℝ) ∧
    ∃ w : BitWord N,
      (coincidences.card : ℝ) / (trials.card : ℝ) ∈
        Set.Icc (finitePrefixReadout (List.ofFn w))
          (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ N) := by
  have hcountPos : 0 < coincidences.card := Finset.card_pos.mpr hne
  have hcountLt : coincidences.card < trials.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hproper⟩)
  have htotalPos : 0 < trials.card := lt_trans hcountPos hcountLt
  have hratioPos : 0 < (coincidences.card : ℝ) / (trials.card : ℝ) :=
    div_pos (by exact_mod_cast hcountPos) (by exact_mod_cast htotalPos)
  have hratioLt : (coincidences.card : ℝ) / (trials.card : ℝ) < 1 :=
    (div_lt_one (by exact_mod_cast htotalPos)).2 (by exact_mod_cast hcountLt)
  refine ⟨congrArg Subtype.val
    (quotientReadout_logOddsCoordinate hratioPos hratioLt), ?_⟩
  exact (finite_coincidence_count_logistic_bitword_bridge
    coincidences.card trials.card hcountPos hcountLt N).2

/-- If a finite relabeling preserves the trial window, it preserves the
coincidence-intersection count and hence its log-odds Cantor readout. This
transports finite counting symmetry into the same quotient used by the
Wheeler and gamma-2 coordinates. -/
theorem coincidence_readout_invariant_under_trial_relabeling
    {α : Type*} [DecidableEq α]
    (e : Equiv α α) (events window : Finset α)
    (hwindow : window.map e.toEmbedding = window) :
    kmsCantorReadout
        (logOddsCoordinate
          (((events.map e.toEmbedding ∩ window).card : ℝ) / (window.card : ℝ))) =
      kmsCantorReadout
        (logOddsCoordinate (((events ∩ window).card : ℝ) / (window.card : ℝ))) := by
  have hcount := SymmetricCounting.projection_invariant e events window hwindow
  rw [hcount]

/-- Complementing a normalized finite count inverts its odds ratio, negates
its log-odds coordinate, and therefore complements its Cantor-readout class. -/
theorem finite_coincidence_count_complement_reflection
    (coincidenceCount totalCount : ℕ)
    (hcount : 0 < coincidenceCount) (hcount_total : coincidenceCount < totalCount) :
    kmsCantorReadout
        (logOddsCoordinate
          (((totalCount - coincidenceCount : ℕ) : ℝ) / (totalCount : ℝ))) =
      readoutComplement
        (kmsCantorReadout
          (logOddsCoordinate ((coincidenceCount : ℝ) / (totalCount : ℝ)))) := by
  have htotal : 0 < (totalCount : ℝ) := by
    exact_mod_cast (lt_trans hcount hcount_total)
  have hcountR : 0 < (coincidenceCount : ℝ) := by exact_mod_cast hcount
  have hcountLt : (coincidenceCount : ℝ) < (totalCount : ℝ) := by
    exact_mod_cast hcount_total
  have hratio : 0 < (coincidenceCount : ℝ) / (totalCount : ℝ) :=
    div_pos hcountR htotal
  have hratio_lt_one :
      (coincidenceCount : ℝ) / (totalCount : ℝ) < 1 :=
    (div_lt_one htotal).2 hcountLt
  have hcast_sub :
      ((totalCount - coincidenceCount : ℕ) : ℝ) =
        (totalCount : ℝ) - (coincidenceCount : ℝ) := by
    exact_mod_cast Nat.cast_sub (Nat.le_of_lt hcount_total)
  have hcomplement :
      (((totalCount - coincidenceCount : ℕ) : ℝ) / (totalCount : ℝ)) =
        1 - (coincidenceCount : ℝ) / (totalCount : ℝ) := by
    rw [hcast_sub]
    field_simp [ne_of_gt htotal]
  have hlog :
      logOddsCoordinate
          (((totalCount - coincidenceCount : ℕ) : ℝ) / (totalCount : ℝ)) =
        -logOddsCoordinate ((coincidenceCount : ℝ) / (totalCount : ℝ)) := by
    rw [hcomplement]
    exact logOddsCoordinate_one_sub hratio hratio_lt_one
  rw [hlog]
  exact kmsCantorReadout_timeReflection
    (logOddsCoordinate ((coincidenceCount : ℝ) / (totalCount : ℝ)))

/-- A complementary finite coincidence count occupies the reflected
length-`N` Cantor cell. The bitword complement acts on the finite cylinder
itself, not only on the quotient class. -/
theorem finite_coincidence_count_complement_bitword_cell
    (coincidenceCount totalCount : ℕ)
    (hcount : 0 < coincidenceCount) (hcount_total : coincidenceCount < totalCount)
    (N : ℕ) (w : BitWord N)
    (hcell : (coincidenceCount : ℝ) / (totalCount : ℝ) ∈
      Set.Icc (finitePrefixReadout (List.ofFn w))
        (finitePrefixReadout (List.ofFn w) + (1 / 2 : ℝ) ^ N)) :
    (((totalCount - coincidenceCount : ℕ) : ℝ) / (totalCount : ℝ)) ∈
      Set.Icc (finitePrefixReadout (List.ofFn (fun i => !w i)))
        (finitePrefixReadout (List.ofFn (fun i => !w i)) + (1 / 2 : ℝ) ^ N) := by
  have htotal : 0 < (totalCount : ℝ) := by
    exact_mod_cast (lt_trans hcount hcount_total)
  have hcast_sub :
      ((totalCount - coincidenceCount : ℕ) : ℝ) =
        (totalCount : ℝ) - (coincidenceCount : ℝ) := by
    exact_mod_cast Nat.cast_sub (Nat.le_of_lt hcount_total)
  have hratioComplement :
      (((totalCount - coincidenceCount : ℕ) : ℝ) / (totalCount : ℝ)) =
        1 - (coincidenceCount : ℝ) / (totalCount : ℝ) := by
    rw [hcast_sub]
    field_simp [ne_of_gt htotal]
  have hprefix := finitePrefixReadout_complementBitWord w
  rw [hratioComplement]
  constructor
  · have hcellUpper := hcell.2
    linarith
  · have hcellLower := hcell.1
    linarith

end InfoGeometry.Canonical.KMSCantorLogisticBridge

end noncomputable section

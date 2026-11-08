/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.OperatorAlgebra.PeirceSpine.PhaseConjugateSteinberg
import InfoGeometry.OperatorAlgebra.PeirceSpine.KMSOperatorMonodromy

/-!
# KMS strip coordinates, critical-strip transport, and operator edge monodromy

This module formalizes the affine coordinate correspondence between a real-time
KMS strip and the open zeta critical strip, the induced four coordinate
reflections, a bounded real compactification coordinate, and an involutive
operator-valued edge transport.  The edge transport is explicit data: this file
does not assert that KMS boundary values are periodic or identify them with a
zeta function.
-/

noncomputable section

namespace InfoGeometry.NCG.KMSStripKleinMonodromy

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open Filter
open scoped Topology

/-- A point of the real-time/imaginary-time plane, in `(t, τ)` coordinates. -/
abbrev StripPoint := ℝ × ℝ

/-- The open KMS strip of height `β`, represented in real coordinates. -/
def inKMSStrip (β : ℝ) (z : StripPoint) : Prop := 0 < z.2 ∧ z.2 < β

/-- The affine chart `s = 1 - τ/β + i t/β` from the KMS strip to the zeta plane. -/
def kmsToZeta (β : ℝ) (z : StripPoint) : ZetaAffineChart :=
  ⟨1 - z.2 / β, z.1 / β⟩

/-- The inverse affine coordinate map from the zeta chart to KMS coordinates. -/
def zetaToKMS (β : ℝ) (s : ZetaAffineChart) : StripPoint :=
  (β * s.tau, β * (1 - s.sigma))

/-- Points in the KMS strip map into the open critical strip. -/
theorem kmsToZeta_maps_strip {β : ℝ} (hβ : 0 < β) {z : StripPoint}
    (hz : inKMSStrip β z) :
    0 < (kmsToZeta β z).sigma ∧ (kmsToZeta β z).sigma < 1 := by
  constructor
  · change 0 < 1 - z.2 / β
    have hdiv : z.2 / β < 1 := (div_lt_one hβ).2 hz.2
    linarith
  · change (1 - z.2 / β) < 1
    have hpos : 0 < z.2 / β := div_pos hz.1 hβ
    linarith

/-- The inverse coordinate sends the open critical strip into the KMS strip. -/
theorem zetaToKMS_maps_criticalStrip {β : ℝ} (hβ : 0 < β) {s : ZetaAffineChart}
    (hs : 0 < s.sigma ∧ s.sigma < 1) :
    inKMSStrip β (zetaToKMS β s) := by
  have hs0 := hs.1
  have hs1 := hs.2
  constructor
  · exact mul_pos hβ (by linarith)
  · calc
      β * (1 - s.sigma) < β * 1 :=
        mul_lt_mul_of_pos_left (by linarith) hβ
      _ = β := by ring

/-- The two affine coordinate maps are inverse on the zeta chart. -/
theorem kmsToZeta_zetaToKMS {β : ℝ} (hβ : 0 < β) (s : ZetaAffineChart) :
    kmsToZeta β (zetaToKMS β s) = s := by
  ext
  · simp [kmsToZeta, zetaToKMS]
    field_simp [ne_of_gt hβ]
    ring
  · simp [kmsToZeta, zetaToKMS]
    field_simp [ne_of_gt hβ]

/-- The two affine coordinate maps are inverse on the KMS plane. -/
theorem zetaToKMS_kmsToZeta {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    zetaToKMS β (kmsToZeta β z) = z := by
  cases z with
  | mk t τ =>
      apply Prod.ext
      · simp [kmsToZeta, zetaToKMS]
        field_simp [ne_of_gt hβ]
      · simp [kmsToZeta, zetaToKMS]
        field_simp [ne_of_gt hβ]

/-- The critical line is the image of the midline of the KMS strip. -/
theorem kmsToZeta_midline {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    (kmsToZeta β (t, β / 2)).sigma = 1 / 2 := by
  simp [kmsToZeta]
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  field_simp
  norm_num

/-- The second KMS coordinate is recovered from the real part of the zeta chart. -/
theorem kmsToZeta_imaginaryTime_recovery {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    z.2 = β * (1 - (kmsToZeta β z).sigma) := by
  simp [kmsToZeta]
  field_simp [ne_of_gt hβ]

/-- The real-time coordinate is recovered from the imaginary part of the chart. -/
theorem kmsToZeta_realTime_recovery {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    z.1 = β * (kmsToZeta β z).tau := by
  simp [kmsToZeta]
  field_simp [ne_of_gt hβ]

/-- Complex conjugation on the zeta chart corresponds to reversing real time. -/
theorem kms_conjugation_transport (β : ℝ) (z : StripPoint) :
    chartConjugation (kmsToZeta β z) = kmsToZeta β (-z.1, z.2) := by
  ext <;> simp [chartConjugation, kmsToZeta, neg_div]

/-- Functional reflection corresponds to reversing real time and exchanging strip edges. -/
theorem kms_functional_reflection_transport {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    chartFunctionalDual (kmsToZeta β z) = kmsToZeta β (-z.1, β - z.2) := by
  ext
  · simp [chartFunctionalDual, kmsToZeta]
    field_simp [ne_of_gt hβ]
    ring
  · simp [chartFunctionalDual, kmsToZeta, neg_div]

/-- The critical mirror exchanges strip edges while preserving real time. -/
theorem kms_critical_mirror_transport {β : ℝ} (hβ : 0 < β) (z : StripPoint) :
    chartCriticalMirror (kmsToZeta β z) = kmsToZeta β (z.1, β - z.2) := by
  ext
  · simp [chartCriticalMirror, kmsToZeta]
    field_simp [ne_of_gt hβ]
    ring
  · simp [chartCriticalMirror, kmsToZeta]

/-- Logistic compactification coordinate for the real-time axis. -/
def compactifiedTime (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

/-- The compactified time lies strictly between its two endpoint values. -/
theorem compactifiedTime_mem_unitInterval (t : ℝ) :
    0 < compactifiedTime t ∧ compactifiedTime t < 1 := by
  have he : 0 < Real.exp t := Real.exp_pos t
  constructor
  · exact div_pos he (by positivity)
  · rw [compactifiedTime, div_lt_one (by positivity)]
    linarith

/-- At `t = 0`, the logistic compactification coordinate takes the midpoint value `1 / 2`. -/
@[simp] theorem compactifiedTime_zero : compactifiedTime 0 = 1 / 2 := by
  unfold compactifiedTime
  rw [Real.exp_zero]
  norm_num

/-- Time reversal `t ↦ -t` corresponds to the unit-interval reflection `x ↦ 1 - x`. -/
theorem compactifiedTime_neg (t : ℝ) :
    compactifiedTime (-t) = 1 - compactifiedTime t := by
  unfold compactifiedTime
  rw [Real.exp_neg]
  have he : 0 < Real.exp t := Real.exp_pos t
  have he_ne : Real.exp t ≠ 0 := ne_of_gt he
  have h1e : 1 + Real.exp t ≠ 0 := by linarith
  have h1einv : 1 + (Real.exp t)⁻¹ ≠ 0 := by
    have : 0 < (Real.exp t)⁻¹ := inv_pos.mpr he
    linarith
  field_simp [he_ne, h1e, h1einv]
  ring

/-- Endpoint limit at `-∞`: `compactifiedTime t → 0` as `t → -∞`. -/
theorem tendsto_compactifiedTime_atBot :
    Filter.Tendsto compactifiedTime Filter.atBot (nhds 0) := by
  unfold compactifiedTime
  have h_num : Filter.Tendsto (fun t : ℝ => Real.exp t) Filter.atBot (nhds 0) :=
    Real.tendsto_exp_atBot
  have h_den : Filter.Tendsto (fun t : ℝ => 1 + Real.exp t) Filter.atBot (nhds (1 + 0)) :=
    tendsto_const_nhds.add Real.tendsto_exp_atBot
  have h_div := h_num.div h_den (by norm_num)
  have h_fun :
      (fun t : ℝ => Real.exp t) / (fun t => 1 + Real.exp t) =
        fun t => Real.exp t / (1 + Real.exp t) := by
    funext t
    rfl
  rw [h_fun] at h_div
  simpa using h_div

/-- Endpoint limit at `+∞`: `compactifiedTime t → 1` as `t → +∞`. -/
theorem tendsto_compactifiedTime_atTop :
    Filter.Tendsto compactifiedTime Filter.atTop (nhds 1) := by
  have h_eq : compactifiedTime = fun t : ℝ => 1 - compactifiedTime (-t) := by
    ext t
    have h := compactifiedTime_neg t
    linarith
  rw [h_eq]
  have h_neg : Filter.Tendsto (fun t : ℝ => compactifiedTime (-t)) Filter.atTop (nhds 0) :=
    tendsto_compactifiedTime_atBot.comp Filter.tendsto_neg_atTop_atBot
  simpa using tendsto_const_nhds.sub h_neg

/-- Folded ring coordinate `4 * compactifiedTime t * (1 - compactifiedTime t) ∈ (0, 1]`,
which maps `t = 0` to `1` and folds both asymptotic ends `t → ±∞` to `0`. -/
def foldedTimeRing (t : ℝ) : ℝ :=
  4 * compactifiedTime t * (1 - compactifiedTime t)

@[simp] theorem foldedTimeRing_zero : foldedTimeRing 0 = 1 := by
  unfold foldedTimeRing
  rw [compactifiedTime_zero]
  norm_num

theorem foldedTimeRing_neg (t : ℝ) : foldedTimeRing (-t) = foldedTimeRing t := by
  unfold foldedTimeRing
  rw [compactifiedTime_neg]
  ring

theorem foldedTimeRing_mem_Ioc (t : ℝ) :
    0 < foldedTimeRing t ∧ foldedTimeRing t ≤ 1 := by
  rcases compactifiedTime_mem_unitInterval t with ⟨h0, h1⟩
  unfold foldedTimeRing
  constructor
  · have h1' : 0 < 1 - compactifiedTime t := by linarith
    positivity
  · have hsq : 0 ≤ (2 * compactifiedTime t - 1) ^ 2 := sq_nonneg _
    linarith

/-- Both asymptotic ends `t → -∞` and `t → +∞` converge to the same glued origin `0`
under `foldedTimeRing`. -/
theorem tendsto_foldedTimeRing_atBot_and_atTop :
    Filter.Tendsto foldedTimeRing Filter.atBot (nhds 0) ∧
    Filter.Tendsto foldedTimeRing Filter.atTop (nhds 0) := by
  constructor
  · unfold foldedTimeRing
    have h1 : Filter.Tendsto (fun t => 4 * compactifiedTime t) Filter.atBot (nhds (4 * 0)) :=
      tendsto_const_nhds.mul tendsto_compactifiedTime_atBot
    have h2 : Filter.Tendsto (fun t => 1 - compactifiedTime t) Filter.atBot (nhds (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_compactifiedTime_atBot
    simpa using h1.mul h2
  · unfold foldedTimeRing
    have h1 : Filter.Tendsto (fun t => 4 * compactifiedTime t) Filter.atTop (nhds (4 * 1)) :=
      tendsto_const_nhds.mul tendsto_compactifiedTime_atTop
    have h2 : Filter.Tendsto (fun t => 1 - compactifiedTime t) Filter.atTop (nhds (1 - 1)) :=
      tendsto_const_nhds.sub tendsto_compactifiedTime_atTop
    simpa using h1.mul h2

/-! ### Topological End-Gluing Quotient (`0 ~ 1`) -/

/-- Equivalence relation identifying the two boundary endpoints `0` and `1` of `[0, 1]`. -/
def EndGluingRel (x y : ℝ) : Prop :=
  x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)

theorem endGluingRel_equivalence : Equivalence EndGluingRel where
  refl x := Or.inl rfl
  symm := by
    rintro x y (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  trans := by
    rintro x y z (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · norm_num at h1
    · subst h2; exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · subst h2; exact Or.inl rfl
    · norm_num at h1

/-- Setoid gluing the asymptotic endpoints `0` and `1`. -/
def endGluingSetoid : Setoid ℝ :=
  ⟨EndGluingRel, endGluingRel_equivalence⟩

/-- The end-glued quotient space identifying the two infinities `0` (`-∞`) and `1` (`+∞`). -/
abbrev EndGluedRing := Quotient endGluingSetoid

/-- In `EndGluedRing`, the two endpoint limits `0` and `1` are topologically identified. -/
theorem endGlued_zero_eq_one :
    (⟦(0 : ℝ)⟧ : EndGluedRing) = ⟦(1 : ℝ)⟧ :=
  Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))

/-- The reflection `x ↦ 1 - x` respects the endpoint gluing `0 ~ 1` and descends to `EndGluedRing`. -/
def endGluedReflect : EndGluedRing → EndGluedRing :=
  Quotient.map (fun x : ℝ => 1 - x) (by
    rintro x y (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · norm_num; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · norm_num; exact Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem endGluedReflect_involutive (q : EndGluedRing) :
    endGluedReflect (endGluedReflect q) = q := by
  refine Quotient.inductionOn q (fun x => ?_)
  apply Quotient.sound
  exact Or.inl (by ring)

theorem endGluedReflect_compactifiedTime (t : ℝ) :
    endGluedReflect ⟦compactifiedTime t⟧ = ⟦compactifiedTime (-t)⟧ := by
  rw [compactifiedTime_neg]
  rfl

section PeirceSteinbergEdgeRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {A : Type*} [Ring A]

/-- Under the Peirce edge transport, one edge crossing inverts the Steinberg braid
`steinbergBraid P B C ↦ steinbergBraidInv P B C`, while two edge crossings restore
`steinbergBraid P B C`. -/
theorem kmsMonodromy_steinbergBraid
    {P : A} (hP : P * P = P) (B C : A) :
    kmsMonodromyIter P 1 (steinbergBraid P B C) =
      steinbergBraidInv P B C ∧
    kmsMonodromyIter P 2 (steinbergBraid P B C) =
      steinbergBraid P B C := by
  constructor
  · change parityConj P (steinbergBraid P B C) = steinbergBraidInv P B C
    exact parityConj_steinbergBraid hP B C
  · exact (kmsMonodromy_even_odd_sheets hP 1 (steinbergBraid P B C)).1

end PeirceSteinbergEdgeRealization

end InfoGeometry.NCG.KMSStripKleinMonodromy

end

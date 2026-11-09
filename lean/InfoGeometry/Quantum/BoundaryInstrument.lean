/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.PositiveBoundaryConditioning
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Positive two-boundary instruments in a full matrix algebra

An instrument has an outcome index and an internal Kraus index. Its conditional
normalizer includes the intervening operation. Nonzero square-root branch
amplitudes characterize precisely when normalization is possible. Completeness
is required only for the success bound, not for normalized outcome weights.
-/

noncomputable section

namespace InfoGeometry.Quantum.BoundaryInstrument

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordered amplitude between two positive matrix boundaries. -/
def branchAmplitude (ρ E K : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt E * K * CFC.sqrt ρ

/-- The branch weight is a Gram trace without any commutation assumption. -/
theorem trace_branchAmplitude {ρ E : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hE : E.PosSemidef) (K : Matrix n n ℂ) :
    trace (branchAmplitude ρ E K * star (branchAmplitude ρ E K)) =
      trace (K * ρ * star K * E) := by
  have hsρ := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have hsE := (CFC.sqrt_nonneg E).posSemidef.isHermitian
  have hgram : branchAmplitude ρ E K * star (branchAmplitude ρ E K) =
      BoundaryConditioning.sandwich (K * ρ * star K) E := by
    unfold branchAmplitude BoundaryConditioning.sandwich
    simp only [star_mul, hsρ.star_eq, hsE.star_eq]
    calc
      _ = CFC.sqrt E * K * (CFC.sqrt ρ * CFC.sqrt ρ) * star K * CFC.sqrt E := by
        noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]; noncomm_ring
  rw [hgram, BoundaryConditioning.trace_sandwich _ hE]

omit [DecidableEq n] in
theorem gram_trace_re_nonneg (C : Matrix n n ℂ) :
    0 ≤ (trace (C * star C)).re :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose C).trace_nonneg).1

/-- A zero real Gram trace detects the zero operator, including empty dimensions. -/
theorem gram_trace_re_eq_zero_iff (C : Matrix n n ℂ) :
    (trace (C * star C)).re = 0 ↔ C = 0 := by
  constructor
  · intro h
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    apply Complex.ext
    · exact h
    · exact (Complex.nonneg_iff.mp
        (Matrix.posSemidef_self_mul_conjTranspose C).trace_nonneg).2.symm
  · intro h
    simp [h]

theorem gram_trace_re_pos_iff (C : Matrix n n ℂ) :
    0 < (trace (C * star C)).re ↔ C ≠ 0 := by
  constructor
  · intro h hz
    simp [hz] at h
  · intro h
    exact lt_of_le_of_ne (gram_trace_re_nonneg C)
      (fun hz => h ((gram_trace_re_eq_zero_iff C).mp hz.symm))

variable {o k : Type*} [Fintype o] [DecidableEq o] [Fintype k] [DecidableEq k]

/-- Sum over the unresolved Kraus index for one observed outcome. -/
def outcomeWeight (V : o → k → Matrix n n ℂ) (ρ E : Matrix n n ℂ) (a : o) : ℝ :=
  (trace (Choi.krausMap (V a) ρ * E)).re

/-- The normalizer for the actual intervening instrument. -/
def normalizer (V : o → k → Matrix n n ℂ) (ρ E : Matrix n n ℂ) : ℝ :=
  ∑ a, outcomeWeight V ρ E a

/-- Conditional outcome probability; normalization theorems require positive `normalizer`. -/
def probability (V : o → k → Matrix n n ℂ) (ρ E : Matrix n n ℂ) (a : o) : ℝ :=
  outcomeWeight V ρ E a / normalizer V ρ E

omit [Fintype o] [DecidableEq o] in
theorem outcomeWeight_nonneg (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef) (a : o) :
    0 ≤ outcomeWeight V ρ E a :=
  (Complex.nonneg_iff.mp (BoundaryConditioning.trace_pairing_nonneg
    (Choi.krausMap_posSemidef (V a) hρ) hE)).1

omit [DecidableEq o] in
theorem normalizer_nonneg (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef) :
    0 ≤ normalizer V ρ E :=
  Finset.sum_nonneg (fun a _ => outcomeWeight_nonneg V hρ hE a)

omit [Fintype o] [DecidableEq o] in
theorem outcomeWeight_eq_sum_gram (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef) (a : o) :
    outcomeWeight V ρ E a =
      ∑ i, (trace (branchAmplitude ρ E (V a i) * star (branchAmplitude ρ E (V a i)))).re := by
  simp only [trace_branchAmplitude hρ hE]
  simp [outcomeWeight, Choi.krausMap, Finset.sum_mul, trace_sum]

omit [Fintype o] [DecidableEq o] in
theorem outcomeWeight_pos_iff (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef) (a : o) :
    0 < outcomeWeight V ρ E a ↔ ∃ i, branchAmplitude ρ E (V a i) ≠ 0 := by
  rw [outcomeWeight_eq_sum_gram V hρ hE a,
    Finset.sum_pos_iff_of_nonneg (fun i _ => gram_trace_re_nonneg _)]
  simp only [Finset.mem_univ, true_and, gram_trace_re_pos_iff]

omit [DecidableEq o] in
/-- Normalization exists exactly when at least one full operator amplitude survives. -/
theorem normalizer_pos_iff (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef) :
    0 < normalizer V ρ E ↔ ∃ a i, branchAmplitude ρ E (V a i) ≠ 0 := by
  rw [normalizer, Finset.sum_pos_iff_of_nonneg (fun a _ => outcomeWeight_nonneg V hρ hE a)]
  simp only [Finset.mem_univ, true_and, outcomeWeight_pos_iff V hρ hE]

theorem normalizer_eq_trace (V : o → k → Matrix n n ℂ) (ρ E : Matrix n n ℂ) :
    normalizer V ρ E =
      (trace (Choi.krausMap (fun p : o × k => V p.1 p.2) ρ * E)).re := by
  simp [normalizer, outcomeWeight, Choi.krausMap, Fintype.sum_prod_type,
    Finset.sum_mul, trace_sum]

omit [DecidableEq o] in
theorem probability_nonneg (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef) (a : o) :
    0 ≤ probability V ρ E a :=
  div_nonneg (outcomeWeight_nonneg V hρ hE a) (normalizer_nonneg V hρ hE)

omit [DecidableEq o] in
theorem sum_probability (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hZ : 0 < normalizer V ρ E) :
    ∑ a, probability V ρ E a = 1 := by
  simp only [probability, ← Finset.sum_div]
  exact div_self (ne_of_gt hZ)

omit [DecidableEq o] in
theorem probability_le_one (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hE : E.PosSemidef)
    (hZ : 0 < normalizer V ρ E) (a : o) : probability V ρ E a ≤ 1 := by
  rw [← sum_probability V hZ]
  exact Finset.single_le_sum (fun b _ => probability_nonneg V hρ hE b) (Finset.mem_univ a)

/-- A complete instrument acting on a density has boundary weight at most one
whenever `E ≤ 1`. Nonnegativity of the weight separately requires `E ≥ 0`. -/
theorem normalizer_le_one (V : o → k → Matrix n n ℂ)
    {ρ E : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (hE : (1 - E).PosSemidef)
    (hV : (∑ p : o × k, star (V p.1 p.2) * V p.1 p.2) = 1) :
    normalizer V ρ E ≤ 1 := by
  let U := fun p : o × k => V p.1 p.2
  have hnonneg := (Complex.nonneg_iff.mp (BoundaryConditioning.trace_pairing_nonneg
    (Choi.krausMap_posSemidef U hρ) hE)).1
  have htrace : trace (Choi.krausMap U ρ) = 1 :=
    (Choi.trace_krausMap_of_completeness U hV ρ).trans htr
  rw [mul_sub, mul_one, trace_sub, Complex.sub_re, htrace, Complex.one_re] at hnonneg
  rw [normalizer_eq_trace]
  exact sub_nonneg.mp hnonneg

/-- The exact disturbance of the bare boundary overlap by an intervening instrument. -/
theorem normalizer_sub_overlap (V : o → k → Matrix n n ℂ) (ρ E : Matrix n n ℂ) :
    normalizer V ρ E - (trace (ρ * E)).re =
      (trace (ρ * (Choi.krausMap (fun p : o × k => star (V p.1 p.2)) E - E))).re := by
  rw [normalizer_eq_trace, Choi.trace_krausMap_pairing]
  simp only [mul_sub, trace_sub, Complex.sub_re]

/-- A backward fixed effect gives the bare overlap; no converse for one input is asserted. -/
theorem normalizer_eq_overlap_of_fixed (V : o → k → Matrix n n ℂ)
    (ρ E : Matrix n n ℂ)
    (hE : Choi.krausMap (fun p : o × k => star (V p.1 p.2)) E = E) :
    normalizer V ρ E = (trace (ρ * E)).re := by
  rw [normalizer_eq_trace, Choi.trace_krausMap_pairing, hE]

/-- Completeness expresses disturbance as a sum of genuine operator commutators. -/
theorem backward_defect_eq_commutators (V : o → k → Matrix n n ℂ)
    (E : Matrix n n ℂ)
    (hV : (∑ p : o × k, star (V p.1 p.2) * V p.1 p.2) = 1) :
    Choi.krausMap (fun p : o × k => star (V p.1 p.2)) E - E =
      ∑ p : o × k, star (V p.1 p.2) * ⁅E, V p.1 p.2⁆ := by
  simp only [Ring.lie_def, mul_sub, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hV, one_mul, Choi.krausMap, LinearMap.coe_mk, AddHom.coe_mk, star_star]

omit [Fintype o] [DecidableEq o] in
/-- Forgetting a complete final effect family recovers the unconditioned outcome weight. -/
theorem sum_effect_outcomeWeight {f : Type*} [Fintype f]
    (V : o → k → Matrix n n ℂ) (ρ : Matrix n n ℂ) (F : f → Matrix n n ℂ)
    (hF : ∑ b, F b = 1) (a : o) :
    ∑ b, outcomeWeight V ρ (F b) a = (trace (Choi.krausMap (V a) ρ)).re := by
  have h : ∑ b, trace (Choi.krausMap (V a) ρ * F b) = trace (Choi.krausMap (V a) ρ) := by
    rw [← trace_sum, ← Finset.mul_sum, hF, mul_one]
  simpa [outcomeWeight] using congrArg Complex.re h

/-- Ordered Kraus composition has the later operator on the left. -/
theorem krausMap_comp {j : Type*} [Fintype j] [DecidableEq j]
    (V : k → Matrix n n ℂ) (W : j → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    Choi.krausMap (fun p : j × k => W p.1 * V p.2) ρ =
      Choi.krausMap W (Choi.krausMap V ρ) := by
  simp only [Choi.krausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type, star_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

end InfoGeometry.Quantum.BoundaryInstrument

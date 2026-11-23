/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.Arithmetic.IdeleClassZetaSymmetry

/-!
# Centered reflection, Cayley coordinates, and finite matrix examples

This module proves elementary identities on `ℂ` and on `2 × 2` matrices. In
particular, `weilPairMode` is only a two-point reflection pairing built from an
arbitrary function `Φ`; it is **not** the classical Weil explicit-formula
pairing, a Krein-space form, or a criterion for RH/GRH. Its unrestricted test
functions make the pointwise positivity equivalence a property of this model.

The Cayley map identities characterize the critical line by a unit-circle
equation. The matrix declarations establish only the displayed finite
identities; they do not connect Jordan blocks to zeta-zero multiplicity or
prove a spectral blow-up limit. For the separate coalescing-eigenvalue
construction, see `Canonical.KreinParabolicSpectralObstructions`.
-/

noncomputable section

open Complex

namespace InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence

open InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart

/-- Centered critical-horizon reflection `w ↦ -star w` (`u + it ↦ -u + it`). -/
def horizonReflect (w : ℂ) : ℂ := -star w

@[simp] theorem horizonReflect_re (w : ℂ) : (horizonReflect w).re = -w.re := by
  simp [horizonReflect]

@[simp] theorem horizonReflect_im (w : ℂ) : (horizonReflect w).im = w.im := by
  simp [horizonReflect]

theorem horizonReflect_involutive (w : ℂ) :
    horizonReflect (horizonReflect w) = w := by
  simp [horizonReflect, star_neg]

/-- Fixed points of `horizonReflect` are precisely points on `w.re = 0`. -/
theorem horizonReflect_fixed_iff_re_eq_zero (w : ℂ) :
    horizonReflect w = w ↔ w.re = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [horizonReflect_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [h]
    · simp

/-- Centered `horizonReflect` intertwines with `CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection`. -/
theorem antiunitaryCriticalReflection_centered (w : ℂ) :
    antiunitaryCriticalReflection (1 / 2 + w) = 1 / 2 + horizonReflect w := by
  apply Complex.ext
  · simp [antiunitaryCriticalReflection, horizonReflect]
    ring
  · simp [antiunitaryCriticalReflection, horizonReflect]

/-- `CriticalLine (1 / 2 + w)` is equivalent to `w.re = 0`. -/
theorem criticalLine_centered_iff_re_eq_zero (w : ℂ) :
    CriticalLine (1 / 2 + w) ↔ w.re = 0 := by
  simp only [CriticalLine, Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
  constructor <;> intro h <;> linarith

/-- Compatibility of `horizonReflect` with `ZetaCenteredChart.criticalMirror` under
`FourierParity.actOnCentered FourierParity.dual`. -/
theorem horizonReflect_eq_centered_criticalMirror (w : ℂ) :
    (⟨(horizonReflect w).re, (horizonReflect w).im⟩ : ZetaCenteredChart) =
      FourierParity.actOnCentered FourierParity.dual ⟨w.re, w.im⟩ := by
  simp [FourierParity.actOnCentered, ZetaCenteredChart.criticalMirror]

/-- Two-point reflection pairing `2 * Re (Φ(w) * conj (Φ(horizonReflect w)))`.
Despite its historical name, this definition is not the global Weil explicit-formula
pairing and carries no test-function topology or summation over zeta zeros. -/
def weilPairMode (w : ℂ) (Φ : ℂ → ℂ) : ℝ :=
  2 * (Φ w * star (Φ (horizonReflect w))).re

/-- At a fixed point of the reflection (`w.re = 0`), this two-point pairing is a
nonnegative norm square. -/
theorem weilPairMode_eq_two_normSq_of_re_eq_zero {w : ℂ} (hw : w.re = 0) (Φ : ℂ → ℂ) :
    weilPairMode w Φ = 2 * Complex.normSq (Φ w) := by
  rw [weilPairMode, (horizonReflect_fixed_iff_re_eq_zero w).mpr hw]
  have hmul : Φ w * star (Φ w) = (Complex.normSq (Φ w) : ℂ) := by
    simp [Complex.mul_conj]
  rw [hmul, Complex.ofReal_re]

/-- Every fixed point of the reflection yields a nonnegative two-point pairing
for every function `Φ`. -/
theorem weilPairMode_nonneg_of_re_eq_zero {w : ℂ} (hw : w.re = 0) (Φ : ℂ → ℂ) :
    0 ≤ weilPairMode w Φ := by
  rw [weilPairMode_eq_two_normSq_of_re_eq_zero hw Φ]
  exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

/-- Every non-fixed point admits a function separating the two evaluation points
whose two-point pairing equals `-2`. This is a property of the unrestricted
function space, not a negative vector in a global Weil/Krein form. -/
theorem exists_negative_weilPairMode_of_re_ne_zero {w : ℂ} (hw : w.re ≠ 0) :
    ∃ Φ : ℂ → ℂ, weilPairMode w Φ = -2 ∧ weilPairMode w Φ < 0 := by
  classical
  let Φ : ℂ → ℂ := fun z ↦ if z = w then 1 else -1
  have hne : horizonReflect w ≠ w := by
    intro h
    exact hw ((horizonReflect_fixed_iff_re_eq_zero w).mp h)
  refine ⟨Φ, ?_, ?_⟩
  · simp [weilPairMode, Φ, hne]
  · simp [weilPairMode, Φ, hne]

/-- In this two-point model, the reflection fixes `w` exactly when every
unrestricted function has nonnegative pairing. -/
theorem re_eq_zero_iff_forall_weilPairMode_nonneg (w : ℂ) :
    w.re = 0 ↔ ∀ Φ : ℂ → ℂ, 0 ≤ weilPairMode w Φ := by
  constructor
  · intro hw Φ
    exact weilPairMode_nonneg_of_re_eq_zero hw Φ
  · intro h
    by_contra hw
    obtain ⟨Φ, _, hneg⟩ := exists_negative_weilPairMode_of_re_ne_zero hw
    exact hneg.not_ge (h Φ)

/-- Finite sum of the two-point reflection pairings over a `Finset ℂ`. -/
def weilConfigForm (S : Finset ℂ) (Φ : ℂ → ℂ) : ℝ :=
  ∑ w ∈ S, weilPairMode w Φ

/-- If every point in a finite set is fixed by reflection, the finite sum is
nonnegative. This does not state a zero-sum explicit formula. -/
theorem weilConfigForm_nonneg_of_all_re_eq_zero (S : Finset ℂ)
    (hS : ∀ w ∈ S, w.re = 0) (Φ : ℂ → ℂ) :
    0 ≤ weilConfigForm S Φ :=
  Finset.sum_nonneg fun w hw ↦ weilPairMode_nonneg_of_re_eq_zero (hS w hw) Φ

/-- Cayley coordinate `z(w) = (w - 1 / 2) / (w + 1 / 2)`. Its unit-circle
boundary is `w.re = 0`; the right half-plane maps inside the disk. -/
def apollonianDiskMap (w : ℂ) : ℂ :=
  (w - 1 / 2) / (w + 1 / 2)

/-- Difference of the squared norms of the two affine factors in the Cayley map. -/
theorem normSq_add_half_sub_normSq_sub_half (w : ℂ) :
    Complex.normSq (w + 1 / 2) - Complex.normSq (w - 1 / 2) = 2 * w.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
    Complex.one_im]
  ring

/-- The signed squared-radius defect is the real part of `w` divided by the
squared denominator. -/
theorem one_sub_normSq_apollonianDiskMap
    (w : ℂ) (hden : w + 1 / 2 ≠ 0) :
    1 - Complex.normSq (apollonianDiskMap w) =
      2 * w.re / Complex.normSq (w + 1 / 2) := by
  have hden_pos : 0 < Complex.normSq (w + 1 / 2) :=
    Complex.normSq_pos.mpr hden
  have hdiv : Complex.normSq (apollonianDiskMap w) =
      Complex.normSq (w - 1 / 2) / Complex.normSq (w + 1 / 2) := by
    simp [apollonianDiskMap]
  rw [hdiv]
  have hpolar := normSq_add_half_sub_normSq_sub_half w
  rw [one_sub_div (ne_of_gt hden_pos), hpolar]

/-- Away from the pole, the Cayley transform lies strictly inside the unit
disk exactly when `w` lies in the right half-plane. -/
theorem normSq_apollonianDiskMap_lt_one_iff_re_pos
    (w : ℂ) (hden : w + 1 / 2 ≠ 0) :
    Complex.normSq (apollonianDiskMap w) < 1 ↔ 0 < w.re := by
  rw [← sub_pos, one_sub_normSq_apollonianDiskMap w hden]
  constructor
  · intro h
    have hden_pos : 0 < Complex.normSq (w + 1 / 2) :=
      Complex.normSq_pos.mpr hden
    have := (div_pos_iff_of_pos_right hden_pos).mp h
    linarith
  · intro h
    exact div_pos (by positivity) (Complex.normSq_pos.mpr hden)

/-- Unconditional unit-circle characterization: `normSq (apollonianDiskMap w) = 1 ↔ w.re = 0`. -/
theorem normSq_apollonianDiskMap_eq_one_iff_re_eq_zero (w : ℂ) :
    Complex.normSq (apollonianDiskMap w) = 1 ↔ w.re = 0 := by
  by_cases hw : w + 1 / 2 = 0
  · have hwval : w = -(1 / 2) := eq_neg_of_add_eq_zero_left hw
    have hre : w.re ≠ 0 := by
      rw [hwval]
      norm_num
    have hnsq : Complex.normSq (apollonianDiskMap w) = 0 := by
      rw [apollonianDiskMap, hw, div_zero, Complex.normSq_zero]
    simp [hnsq, hre]
  · have hpos : 0 < Complex.normSq (w + 1 / 2) := Complex.normSq_pos.mpr hw
    have hdiv : Complex.normSq (apollonianDiskMap w) =
        Complex.normSq (w - 1 / 2) / Complex.normSq (w + 1 / 2) := by
      simp [apollonianDiskMap]
    rw [hdiv, div_eq_one_iff_eq hpos.ne']
    have hpol := normSq_add_half_sub_normSq_sub_half w
    constructor <;> intro h <;> linarith

/-- Sign negation on centered `w` corresponds to inversion `z ↦ z⁻¹` on the Apollonian disk. -/
theorem apollonianDiskMap_neg (w : ℂ) :
    apollonianDiskMap (-w) = (apollonianDiskMap w)⁻¹ := by
  have hnum : -w - 1 / 2 = -(w + 1 / 2) := by ring
  have hden : -w + 1 / 2 = -(w - 1 / 2) := by ring
  rw [apollonianDiskMap, apollonianDiskMap, hnum, hden, neg_div_neg_eq, inv_div]

/-- Horizon reflection `w ↦ -star w` intertwines via `apollonianDiskMap` with anti-holomorphic
unit-circle inversion `z ↦ (star z)⁻¹`. -/
theorem apollonianDiskMap_horizonReflect (w : ℂ) :
    apollonianDiskMap (horizonReflect w) = (star (apollonianDiskMap w))⁻¹ := by
  have hst1 : -star w - 1 / 2 = -star (w + 1 / 2) := by
    rw [star_add, show star (1 / 2 : ℂ) = 1 / 2 by simp]
    ring
  have hst2 : -star w + 1 / 2 = -star (w - 1 / 2) := by
    rw [star_sub, show star (1 / 2 : ℂ) = 1 / 2 by simp]
    ring
  rw [apollonianDiskMap, apollonianDiskMap, horizonReflect, hst1, hst2, neg_div_neg_eq,
    star_div₀, inv_div]

/-- If `z` is on the unit circle, then `(1 - z^n).re ≥ 0` for every natural
number `n`. This elementary inequality alone is not Li's criterion for RH. -/
theorem re_one_sub_pow_nonneg_of_normSq_eq_one {z : ℂ} (hz : Complex.normSq z = 1) (n : ℕ) :
    0 ≤ (1 - z ^ n).re := by
  have hnorm : ‖z‖ = 1 := by
    simp [Complex.norm_def, hz]
  have hpow : ‖z ^ n‖ = 1 := by
    rw [norm_pow, hnorm, one_pow]
  have hre : (z ^ n).re ≤ 1 := by
    calc
      (z ^ n).re ≤ ‖z ^ n‖ := Complex.re_le_norm (z ^ n)
      _ = 1 := hpow
  simp only [Complex.sub_re, Complex.one_re, sub_nonneg]
  exact hre

/-- For a non-fixed point away from the two zeros/pole of the Cayley numerator
and denominator, either this coordinate or its reflected coordinate has squared
norm greater than one. No Li-coefficient or exponential-negativity conclusion
is asserted. -/
theorem apollonianDiskMap_unit_dichotomy_of_re_ne_zero {w : ℂ}
    (hwre : w.re ≠ 0) (hm : w - 1 / 2 ≠ 0) (hp : w + 1 / 2 ≠ 0) :
    1 < Complex.normSq (apollonianDiskMap w) ∨
      1 < Complex.normSq (apollonianDiskMap (-w)) := by
  have hne : Complex.normSq (apollonianDiskMap w) ≠ 1 := by
    intro h
    exact hwre ((normSq_apollonianDiskMap_eq_one_iff_re_eq_zero w).mp h)
  have hzero : apollonianDiskMap w ≠ 0 := div_ne_zero hm hp
  have hpos : 0 < Complex.normSq (apollonianDiskMap w) := Complex.normSq_pos.mpr hzero
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · right
    rw [apollonianDiskMap_neg, Complex.normSq_inv]
    exact (one_lt_inv₀ hpos).mpr hlt
  · exact Or.inl hgt

/-- Generic `2 × 2` Jordan block with eigenvalue `ρ`. Its algebraic form alone
does not identify `ρ` with a zero of any analytic function. -/
def parabolicJordanBlock (ρ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![ρ, 1], ![0, ρ]]

/-- The nonzero nilpotent part of the generic Jordan block. -/
def jordanNilpotentDefect : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1], ![0, 0]]

theorem parabolicJordanBlock_sub_scalar (ρ : ℂ) :
    parabolicJordanBlock ρ - ρ • (1 : Matrix (Fin 2) (Fin 2) ℂ) = jordanNilpotentDefect := by
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;> simp [parabolicJordanBlock, jordanNilpotentDefect]

theorem jordanNilpotentDefect_ne_zero : jordanNilpotentDefect ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [jordanNilpotentDefect] at h01

theorem jordanNilpotentDefect_sq_eq_zero :
    jordanNilpotentDefect * jordanNilpotentDefect = 0 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [jordanNilpotentDefect]

/-- Diagonal signature matrix `diag(1,-1)`. The following theorem records its
involution and trace; it does not assert a nuclear-norm identity. -/
def splitKreinMetric : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0], ![0, -1]]

theorem splitKreinMetric_sq_eq_one :
    splitKreinMetric * splitKreinMetric = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [splitKreinMetric]

theorem splitKreinMetric_trace_eq_zero :
    Matrix.trace splitKreinMetric = 0 := by
  dsimp [Matrix.trace, Matrix.diag]
  rw [Fin.sum_univ_two]
  simp [splitKreinMetric]

/-- Rank-one idempotent matrix `[[1,c],[0,0]]`. The parameter `c` is free;
this definition does not tie it to an angle or to coalescing eigenvalues. -/
def obliqueProjector (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, c], ![0, 0]]

theorem obliqueProjector_idempotent (c : ℝ) :
    obliqueProjector c * obliqueProjector c = obliqueProjector c := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [obliqueProjector]

theorem obliqueProjector_offDiag_sq (c : ℝ) :
    (obliqueProjector c 0 1) ^ 2 = c ^ 2 := by
  simp [obliqueProjector]

/-- The nilpotent matrix does not commute with its transpose. -/
theorem jordanNilpotentDefect_noncomm_with_transpose :
    jordanNilpotentDefect * Matrix.transpose jordanNilpotentDefect ≠
      Matrix.transpose jordanNilpotentDefect * jordanNilpotentDefect := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h00
  simp_rw [Matrix.transpose_apply] at h00
  simp [jordanNilpotentDefect] at h00

/-- The diagonal signature matrix does not commute with this idempotent when
its off-diagonal parameter is nonzero. -/
theorem splitKreinMetric_obliqueProjector_noncomm {c : ℝ} (hc : c ≠ 0) :
    splitKreinMetric * obliqueProjector c ≠ obliqueProjector c * splitKreinMetric := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two] at h01
  simp [splitKreinMetric, obliqueProjector] at h01
  exact hc (by linarith)

/-- Closed noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem exists_complexMatrix_noncomm_pair :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨jordanNilpotentDefect, Matrix.transpose jordanNilpotentDefect,
    jordanNilpotentDefect_noncomm_with_transpose⟩

/-- Closed noncommutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem exists_realMatrix_noncomm_pair :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨splitKreinMetric, obliqueProjector 1, splitKreinMetric_obliqueProjector_noncomm one_ne_zero⟩

end InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence

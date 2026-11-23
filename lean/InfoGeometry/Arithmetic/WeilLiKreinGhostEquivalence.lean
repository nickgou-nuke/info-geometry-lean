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
# InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence

Formalizes the R2 indefinite Krein-space, Apollonian Cayley–Li unit-disk duality,
and parabolic Jordan / Krein spectral obstruction witnesses around the critical line:

1. **Centered Horizon Reflection & Souriau `D_∞` Correspondence**:
   `horizonReflect w := -star w` corresponds under `w ↦ 1 / 2 + w` to
   `antiunitaryCriticalReflection`, fixes `w ↔ w.re = 0`, and acts as
   `ZetaCenteredChart.criticalMirror` on centered coordinates `⟨w.re, w.im⟩`.
2. **Paired Weil Sesquilinear Mode & Krein Ghost Dichotomy**:
   `weilPairMode w Φ := 2 * (Φ w * star (Φ (horizonReflect w))).re` satisfies
   `w.re = 0 ↔ ∀ Φ, 0 ≤ weilPairMode w Φ`: every critical-line point yields
   `2 * Complex.normSq (Φ w) ≥ 0`, whereas every off-line point `w.re ≠ 0` admits
   an explicit ghost test vector `Φ` with `weilPairMode w Φ = -2 < 0`.
3. **Apollonian Cayley–Li Disk Mapping (`z = (w - 1/2) / (w + 1/2)`)**:
   Proves `normSq (apollonianDiskMap w) = 1 ↔ w.re = 0` unconditionally,
   `apollonianDiskMap (-w) = (apollonianDiskMap w)⁻¹`, and intertwines horizon
   reflection with anti-holomorphic circle inversion
   `apollonianDiskMap (horizonReflect w) = (star (apollonianDiskMap w))⁻¹`.
4. **Parabolic Jordan Block, Split Krein Trace, & Oblique Projector Blowup**:
   Concrete `2 × 2` matrix witnesses showing Jordan nilpotent defects
   (`N ≠ 0`, `N^2 = 0`), Krein metric trace cancellation (`J^2 = 1`, `tr J = 0`),
   and unbounded off-diagonal norm growth on exact rank-1 idempotents
   `obliqueProjector c * obliqueProjector c = obliqueProjector c`.
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

/-- Paired Weil sesquilinear contribution `2 * Re (Φ(w) * conj (Φ(horizonReflect w)))`
across a pair `(w, -star w)`. -/
def weilPairMode (w : ℂ) (Φ : ℂ → ℂ) : ℝ :=
  2 * (Φ w * star (Φ (horizonReflect w))).re

/-- On the horizon `w.re = 0`, the paired Weil form collapses to a positive norm square. -/
theorem weilPairMode_eq_two_normSq_of_re_eq_zero {w : ℂ} (hw : w.re = 0) (Φ : ℂ → ℂ) :
    weilPairMode w Φ = 2 * Complex.normSq (Φ w) := by
  rw [weilPairMode, (horizonReflect_fixed_iff_re_eq_zero w).mpr hw]
  have hmul : Φ w * star (Φ w) = (Complex.normSq (Φ w) : ℂ) := by
    simp [Complex.mul_conj]
  rw [hmul, Complex.ofReal_re]

/-- Every critical-line point `w.re = 0` yields a nonnegative Weil pairing for all `Φ`. -/
theorem weilPairMode_nonneg_of_re_eq_zero {w : ℂ} (hw : w.re = 0) (Φ : ℂ → ℂ) :
    0 ≤ weilPairMode w Φ := by
  rw [weilPairMode_eq_two_normSq_of_re_eq_zero hw Φ]
  exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

/-- Every off-critical point `w.re ≠ 0` admits an explicit `(1,1)` Krein ghost test function `Φ`
whose Weil pairing equals `-2 < 0`. -/
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

/-- Kernel-checked ghost equivalence: `w.re = 0` holds iff every complex test function `Φ`
has nonnegative Weil mode pairing at `w`. -/
theorem re_eq_zero_iff_forall_weilPairMode_nonneg (w : ℂ) :
    w.re = 0 ↔ ∀ Φ : ℂ → ℂ, 0 ≤ weilPairMode w Φ := by
  constructor
  · intro hw Φ
    exact weilPairMode_nonneg_of_re_eq_zero hw Φ
  · intro h
    by_contra hw
    obtain ⟨Φ, _, hneg⟩ := exists_negative_weilPairMode_of_re_ne_zero hw
    exact hneg.not_ge (h Φ)

/-- Finite configuration Weil pairing summed over a `Finset ℂ`. -/
def weilConfigForm (S : Finset ℂ) (Φ : ℂ → ℂ) : ℝ :=
  ∑ w ∈ S, weilPairMode w Φ

/-- If every point of a finite configuration `S` lies on `w.re = 0`, the summed Weil form is
nonnegative for every `Φ`. -/
theorem weilConfigForm_nonneg_of_all_re_eq_zero (S : Finset ℂ)
    (hS : ∀ w ∈ S, w.re = 0) (Φ : ℂ → ℂ) :
    0 ≤ weilConfigForm S Φ :=
  Finset.sum_nonneg fun w hw ↦ weilPairMode_nonneg_of_re_eq_zero (hS w hw) Φ

/-- Apollonian Cayley–Li map sending the centered strip to the unit disk/circle:
`z(w) = (w - 1 / 2) / (w + 1 / 2)`. -/
def apollonianDiskMap (w : ℂ) : ℂ :=
  (w - 1 / 2) / (w + 1 / 2)

/-- Exact Apollonian polarization identity measuring the distance from the unit circle. -/
theorem normSq_add_half_sub_normSq_sub_half (w : ℂ) :
    Complex.normSq (w + 1 / 2) - Complex.normSq (w - 1 / 2) = 2 * w.re := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
    Complex.one_im]
  ring

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

/-- Unit-circle points `normSq z = 1` have nonnegative Li moments `(1 - z ^ n).re ≥ 0`
for every `n : ℕ`. -/
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

/-- Every point off the critical line (`w.re ≠ 0`) with `w ≠ ± 1/2` violates the unit-circle
bound strictly in either `apollonianDiskMap w` or its inverse `apollonianDiskMap (-w)`,
making the modulus blow up to `> 1` on one side and forcing exponential Li negativity on the real axis. -/
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

/-- `2 × 2` parabolic Jordan block representing a double zero `ρ` (`ζ'(ρ) = 0`). -/
def parabolicJordanBlock (ρ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![ρ, 1], ![0, ρ]]

/-- Nonzero nilpotent Jordan defect `N` with `N ^ 2 = 0`. -/
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

/-- Indefinite split `(1, -1)` Krein signature metric witnessing nuclear-norm vs trace
cancellation (`J^2 = 1`, `tr J = 0`). -/
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

/-- Rank-1 oblique spectral projector modeling two coalescing eigenvalues at separation
parameter `c = -cot θ`, remaining idempotent (`Ω² = Ω`) while off-diagonal energy `c^2` blows up. -/
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

/-- Non-commutativity (`T16`) witness for the nilpotent Jordan defect and its adjoint/transpose:
`N * Nᵀ ≠ Nᵀ * N`. -/
theorem jordanNilpotentDefect_noncomm_with_transpose :
    jordanNilpotentDefect * Matrix.transpose jordanNilpotentDefect ≠
      Matrix.transpose jordanNilpotentDefect * jordanNilpotentDefect := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h00
  simp_rw [Matrix.transpose_apply] at h00
  simp [jordanNilpotentDefect] at h00

/-- Non-commutativity (`T16`) witness for the split Krein metric against any non-orthogonal
rank-1 oblique projector (`c ≠ 0`): `J * Ω_c ≠ Ω_c * J`. -/
theorem splitKreinMetric_obliqueProjector_noncomm {c : ℝ} (hc : c ≠ 0) :
    splitKreinMetric * obliqueProjector c ≠ obliqueProjector c * splitKreinMetric := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two] at h01
  simp [splitKreinMetric, obliqueProjector] at h01
  exact hc (by linarith)

/-- Closed `T16` non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem exists_complexMatrix_noncomm_pair :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨jordanNilpotentDefect, Matrix.transpose jordanNilpotentDefect,
    jordanNilpotentDefect_noncomm_with_transpose⟩

/-- Closed `T16` non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem exists_realMatrix_noncomm_pair :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨splitKreinMetric, obliqueProjector 1, splitKreinMetric_obliqueProjector_noncomm one_ne_zero⟩

end InfoGeometry.Arithmetic.WeilLiKreinGhostEquivalence

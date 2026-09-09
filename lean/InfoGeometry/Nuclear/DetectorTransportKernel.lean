import Mathlib

/-!
# A first-collision transport kernel for a solid cylindrical detector

`Point` carries native product Lebesgue volume. Euclidean squared distances are
explicit coordinate polynomials; the product space's max norm is NOT used as
an inverse-square propagation distance.

The solid, homogeneous cylinder has front face z = 0 and back face z = L.
The isotropic point source is (0, 0, -d), with d > 0. No bore, dead layer,
external scattering, or detector-specific acceptance is hidden in this kernel.
The continuation/acceptance function is supplied in DetectorVolumeResponse.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DetectorTransportKernel

open Set MeasureTheory

abbrev Point := (ℝ × ℝ) × ℝ

/-- Closed transverse disk in native real coordinates. -/
def transverseDisk (R : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ R ^ 2}

/-- Physical support of the solid cylinder. -/
def cylinder (R L : ℝ) : Set Point :=
  transverseDisk R ×ˢ Icc 0 L

/-- Squared Euclidean source-to-interaction distance, not a product max norm. -/
def rangeSq (d : ℝ) (p : Point) : ℝ :=
  p.1.1 ^ 2 + p.1.2 ^ 2 + (d + p.2) ^ 2

def sourceRange (d : ℝ) (p : Point) : ℝ :=
  Real.sqrt (rangeSq d p)

/-- Length inside germanium from the front-face entrance to p. -/
def materialPath (d : ℝ) (p : Point) : ℝ :=
  p.2 * sourceRange d p / (d + p.2)

/-- Front-face intersection of the line from the source to p. -/
def entrance (d : ℝ) (p : Point) : Point :=
  ((d * p.1.1 / (d + p.2), d * p.1.2 / (d + p.2)), 0)

/-- Squared Euclidean distance between two spatial points. -/
def separationSq (p q : Point) : ℝ :=
  (p.1.1 - q.1.1) ^ 2 + (p.1.2 - q.1.2) ^ 2 + (p.2 - q.2) ^ 2

/-- First-collision probability per unit Cartesian volume, per emitted photon.
Here μ is a linear attenuation coefficient, not a mass attenuation coefficient. -/
def firstCollisionKernel (μ d : ℝ) (p : Point) : ℝ :=
  μ * Real.exp (-μ * materialPath d p) / (4 * Real.pi * rangeSq d p)

theorem isClosed_transverseDisk (R : ℝ) : IsClosed (transverseDisk R) := by
  exact isClosed_le (by fun_prop) continuous_const

theorem isCompact_transverseDisk (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (transverseDisk R) := by
  apply (isCompact_Icc : IsCompact (Icc (-R, -R) (R, R))).of_isClosed_subset
    (isClosed_transverseDisk R)
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ R ^ 2 at hq
  change (-R ≤ q.1 ∧ -R ≤ q.2) ∧ (q.1 ≤ R ∧ q.2 ≤ R)
  have hx : q.1 ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg q.2]
  have hy : q.2 ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg q.1]
  constructor
  · constructor <;> nlinarith
  · constructor <;> nlinarith

theorem isClosed_cylinder (R L : ℝ) : IsClosed (cylinder R L) := by
  exact (isClosed_transverseDisk R).prod isClosed_Icc

theorem measurableSet_cylinder (R L : ℝ) : MeasurableSet (cylinder R L) :=
  (isClosed_cylinder R L).measurableSet

theorem isCompact_cylinder (R L : ℝ) (hR : 0 ≤ R) :
    IsCompact (cylinder R L) :=
  (isCompact_transverseDisk R hR).prod isCompact_Icc

theorem axial_gap_pos {d : ℝ} {p : Point} (hd : 0 < d) (hz : 0 ≤ p.2) :
    0 < d + p.2 := by linarith

theorem rangeSq_pos {d : ℝ} {p : Point} (hd : 0 < d) (hz : 0 ≤ p.2) :
    0 < rangeSq d p := by
  have h := sq_pos_of_pos (axial_gap_pos hd hz)
  unfold rangeSq
  nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]

theorem rangeSq_ge_front {d : ℝ} {p : Point} (hd : 0 ≤ d) (hz : 0 ≤ p.2) :
    d ^ 2 ≤ rangeSq d p := by
  unfold rangeSq
  nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2, sq_nonneg p.2, mul_nonneg hd hz]

theorem sourceRange_sq {d : ℝ} {p : Point} (hd : 0 < d) (hz : 0 ≤ p.2) :
    sourceRange d p ^ 2 = rangeSq d p := by
  exact Real.sq_sqrt (le_of_lt (rangeSq_pos hd hz))

theorem materialPath_nonneg {d : ℝ} {p : Point} (hd : 0 < d) (hz : 0 ≤ p.2) :
    0 ≤ materialPath d p := by
  unfold materialPath sourceRange
  exact div_nonneg (mul_nonneg hz (Real.sqrt_nonneg _))
    (le_of_lt (axial_gap_pos hd hz))

/-- The prescribed path length really squares to the entrance-to-point
Euclidean distance. The front-face ray geometry is not an arbitrary depth weight. -/
theorem materialPath_sq_eq_separationSq {d : ℝ} {p : Point}
    (hd : 0 < d) (hz : 0 ≤ p.2) :
    materialPath d p ^ 2 = separationSq p (entrance d p) := by
  have hgap : d + p.2 ≠ 0 := ne_of_gt (axial_gap_pos hd hz)
  have hs := sourceRange_sq hd hz
  unfold materialPath separationSq entrance
  dsimp only
  rw [div_pow, mul_pow, hs]
  unfold rangeSq
  field_simp [hgap] <;> ring

theorem materialPath_on_axis {d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z) :
    materialPath d ((0, 0), z) = z := by
  have hgap : 0 < d + z := by linarith
  have hsq : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 + (d + z) ^ 2 = (d + z) ^ 2 := by ring
  unfold materialPath sourceRange rangeSq
  dsimp
  rw [hsq, Real.sqrt_sq (le_of_lt hgap)]
  exact mul_div_cancel_right₀ z (ne_of_gt hgap)

/-- The positive path length equals the Euclidean length from the entrance. -/
theorem materialPath_eq_sqrt_separationSq {d : ℝ} {p : Point}
    (hd : 0 < d) (hz : 0 ≤ p.2) :
    materialPath d p = Real.sqrt (separationSq p (entrance d p)) := by
  rw [← materialPath_sq_eq_separationSq hd hz]
  exact (Real.sqrt_sq (materialPath_nonneg hd hz)).symm

/-- The source-to-point ray enters through the front disk, not the side wall. -/
theorem entrance_mem_cylinder {d R L : ℝ} {p : Point}
    (hd : 0 < d) (hL : 0 ≤ L) (hp : p ∈ cylinder R L) :
    entrance d p ∈ cylinder R L := by
  have hgap : 0 < d + p.2 := axial_gap_pos hd hp.2.1
  have hc0 : 0 ≤ d / (d + p.2) := div_nonneg hd.le hgap.le
  have hc1 : d / (d + p.2) ≤ 1 := by
    apply (div_le_one hgap).mpr
    linarith [hp.2.1]
  have hc2 : (d / (d + p.2)) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  constructor
  · change (d * p.1.1 / (d + p.2)) ^ 2 + (d * p.1.2 / (d + p.2)) ^ 2 ≤ R ^ 2
    calc
      _ = (d / (d + p.2)) ^ 2 * (p.1.1 ^ 2 + p.1.2 ^ 2) := by ring
      _ ≤ p.1.1 ^ 2 + p.1.2 ^ 2 := mul_le_of_le_one_left (by positivity) hc2
      _ ≤ R ^ 2 := hp.1
  · exact ⟨le_rfl, hL⟩

theorem continuous_rangeSq (d : ℝ) : Continuous (rangeSq d) := by
  unfold rangeSq
  fun_prop

theorem continuous_sourceRange (d : ℝ) : Continuous (sourceRange d) :=
  (continuous_rangeSq d).sqrt

theorem continuousOn_materialPath (R L d : ℝ) (hd : 0 < d) :
    ContinuousOn (materialPath d) (cylinder R L) := by
  unfold materialPath
  apply ContinuousOn.div
  · exact continuous_snd.continuousOn.mul (continuous_sourceRange d).continuousOn
  · fun_prop
  · intro p hp
    exact ne_of_gt (axial_gap_pos hd hp.2.1)

theorem continuousOn_firstCollisionKernel (R L μ d : ℝ) (hd : 0 < d) :
    ContinuousOn (firstCollisionKernel μ d) (cylinder R L) := by
  have hp := continuousOn_materialPath R L d hd
  unfold firstCollisionKernel
  apply ContinuousOn.div
  · exact continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hp))
  · exact continuousOn_const.mul (continuous_rangeSq d).continuousOn
  · intro p hp
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (ne_of_gt (rangeSq_pos hd hp.2.1))

theorem firstCollisionKernel_nonneg {μ d : ℝ} {p : Point}
    (hμ : 0 ≤ μ) (hd : 0 < d) (hz : 0 ≤ p.2) :
    0 ≤ firstCollisionKernel μ d p := by
  unfold firstCollisionKernel
  exact div_nonneg (mul_nonneg hμ (Real.exp_pos _).le)
    (le_of_lt (mul_pos (mul_pos (by norm_num) Real.pi_pos) (rangeSq_pos hd hz)))

/-- A finite, geometry-explicit domination bound. This is not the sharp
solid-angle probability bound. -/
theorem firstCollisionKernel_le_front {μ d : ℝ} {p : Point}
    (hμ : 0 ≤ μ) (hd : 0 < d) (hz : 0 ≤ p.2) :
    firstCollisionKernel μ d p ≤ μ / (4 * Real.pi * d ^ 2) := by
  have he : Real.exp (-μ * materialPath d p) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hμ) (materialPath_nonneg hd hz)
  have hc : 0 < 4 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hden : 0 < 4 * Real.pi * rangeSq d p := mul_pos hc (rangeSq_pos hd hz)
  unfold firstCollisionKernel
  calc
    μ * Real.exp (-μ * materialPath d p) / (4 * Real.pi * rangeSq d p)
        ≤ μ / (4 * Real.pi * rangeSq d p) := by
          apply div_le_div_of_nonneg_right _ hden.le
          simpa only [mul_one] using mul_le_mul_of_nonneg_left he hμ
    _ ≤ μ / (4 * Real.pi * d ^ 2) := by
      exact div_le_div_of_nonneg_left hμ (mul_pos hc (sq_pos_of_pos hd))
        (mul_le_mul_of_nonneg_left (rangeSq_ge_front hd.le hz) hc.le)

end InfoGeometry.Nuclear.DetectorTransportKernel

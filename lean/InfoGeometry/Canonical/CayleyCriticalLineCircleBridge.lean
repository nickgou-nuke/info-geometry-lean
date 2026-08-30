import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

The theorem-safe Cayley/Mobius geometry behind the Lee--Yang/Riemann
dictionary.

This file proves only the elementary conformal geometry:

* `z = s / (1 - s)` sends the Riemann critical line to the unit circle;
* `s = z / (1 + z)` sends the unit circle, away from `z = -1`, back to the
  critical line;
* `s ↦ 1 - s` corresponds to fugacity inversion `z ↦ z⁻¹`.

It does not prove Lee--Yang admissibility for a prime gas, analytic
continuation of zeta, a completed-`xi` determinant identity, or RH.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Cayley/Mobius coordinate from Riemann temperature `s` to fugacity `z`. -/
def cayleyToFugacity (s : ℂ) : ℂ :=
  s / (1 - s)

/-- Inverse Cayley/Mobius coordinate from fugacity `z` to Riemann temperature `s`. -/
def cayleyToTemperature (z : ℂ) : ℂ :=
  z / (1 + z)

/-- The Riemann critical-line real-part condition. -/
def OnCriticalLine (s : ℂ) : Prop :=
  s.re = (1 / 2 : ℝ)

/-- The Lee--Yang unit-circle condition, expressed by squared norm. -/
def OnLeeYangCircle (z : ℂ) : Prop :=
  Complex.normSq z = 1

def criticalLineSet : Set ℂ :=
  {s | OnCriticalLine s}

def unitCircleSet : Set ℂ :=
  {z | OnLeeYangCircle z}

/-! ## Midpoint Apollonius geometry for the critical line -/

/-- Squared distance from `σ + i t` to the zero `3 / 2` on the real axis. -/
def apolloniusNumerator (σ t : ℝ) : ℝ :=
  (σ - 3 / 2) ^ 2 + t ^ 2

/-- Squared distance from `σ + i t` to the pole `-1 / 2` on the real axis. -/
def apolloniusDenominator (σ t : ℝ) : ℝ :=
  (σ + 1 / 2) ^ 2 + t ^ 2

/--
For the midpoint pair `(-1/2, 3/2)`, the Apollonius numerator-minus-denominator
difference is affine in the real coordinate and independent of the imaginary
height.
-/
theorem apollonius_difference (σ t : ℝ) :
    apolloniusNumerator σ t - apolloniusDenominator σ t = -4 * σ + 2 := by
  dsimp [apolloniusNumerator, apolloniusDenominator]
  ring

/--
The unit Apollonius level set for the midpoint pair `(-1/2, 3/2)` is exactly
the critical vertical line `σ = 1/2`.
-/
theorem apollonius_unitary_level_set_iff (σ t : ℝ) :
    apolloniusNumerator σ t = apolloniusDenominator σ t ↔ σ = 1 / 2 := by
  have hdiff := apollonius_difference σ t
  constructor
  · intro h
    have hzero : apolloniusNumerator σ t - apolloniusDenominator σ t = 0 :=
      sub_eq_zero.mpr h
    rw [hdiff] at hzero
    linarith
  · intro h
    have hzero : apolloniusNumerator σ t - apolloniusDenominator σ t = 0 := by
      rw [hdiff, h]
      ring
    exact sub_eq_zero.mp hzero

/--
The strict interior Apollonius inequality for the midpoint pair `(-1/2, 3/2)`
is exactly the right half-plane `σ > 1/2`.
-/
theorem apollonius_lt_iff_right_of_critical (σ t : ℝ) :
    apolloniusNumerator σ t < apolloniusDenominator σ t ↔ 1 / 2 < σ := by
  have hdiff := apollonius_difference σ t
  constructor
  · intro h
    have hneg : apolloniusNumerator σ t - apolloniusDenominator σ t < 0 :=
      sub_neg.mpr h
    rw [hdiff] at hneg
    linarith
  · intro h
    have hneg : apolloniusNumerator σ t - apolloniusDenominator σ t < 0 := by
      rw [hdiff]
      linarith
    exact sub_neg.mp hneg

/--
The strict exterior Apollonius inequality for the midpoint pair `(-1/2, 3/2)`
is exactly the left half-plane `σ < 1/2`.
-/
theorem apollonius_gt_iff_left_of_critical (σ t : ℝ) :
    apolloniusNumerator σ t > apolloniusDenominator σ t ↔ σ < 1 / 2 := by
  have hdiff := apollonius_difference σ t
  constructor
  · intro h
    have hpos : 0 < apolloniusNumerator σ t - apolloniusDenominator σ t :=
      sub_pos.mpr h
    rw [hdiff] at hpos
    linarith
  · intro h
    have hpos : 0 < apolloniusNumerator σ t - apolloniusDenominator σ t := by
      rw [hdiff]
      linarith
    exact sub_pos.mp hpos

/--
The Cayley maps are inverse away from the pole `s = 1`.

Lean's field division is total, so the pole is recorded explicitly as a
property.
-/
theorem cayleyToTemperature_cayleyToFugacity
    (s : ℂ)
    (hs : 1 - s ≠ 0) :
    cayleyToTemperature (cayleyToFugacity s) = s := by
  unfold cayleyToTemperature cayleyToFugacity
  field_simp [hs]
  ring

/--
The inverse Cayley maps are inverse away from the pole `z = -1`.

Lean's field division is total, so the pole is recorded explicitly as a
property.
-/
theorem cayleyToFugacity_cayleyToTemperature
    (z : ℂ)
    (hz : 1 + z ≠ 0) :
    cayleyToFugacity (cayleyToTemperature z) = z := by
  unfold cayleyToFugacity cayleyToTemperature
  field_simp [hz]
  ring

theorem cayleyToFugacity_injective_of_ne_one
    {s t : ℂ} (hs : 1 - s ≠ 0) (ht : 1 - t ≠ 0)
    (h : cayleyToFugacity s = cayleyToFugacity t) :
    s = t := by
  have h' := congrArg cayleyToTemperature h
  rw [cayleyToTemperature_cayleyToFugacity s hs,
    cayleyToTemperature_cayleyToFugacity t ht] at h'
  exact h'

theorem cayleyToTemperature_injective_of_ne_neg_one
    {z w : ℂ} (hz : 1 + z ≠ 0) (hw : 1 + w ≠ 0)
    (h : cayleyToTemperature z = cayleyToTemperature w) :
    z = w := by
  have h' := congrArg cayleyToFugacity h
  rw [cayleyToFugacity_cayleyToTemperature z hz,
    cayleyToFugacity_cayleyToTemperature w hw] at h'
  exact h'

/--
The Cayley transform maps the critical line to the Lee--Yang unit circle.

This is the algebraic core of the dictionary
`Re(s) = 1/2` ↔ `|z| = 1`, with `z = s / (1 - s)`.
-/
theorem cayleyToFugacity_mem_unitCircle_of_criticalLine
    (s : ℂ)
    (hs : OnCriticalLine s) :
    OnLeeYangCircle (cayleyToFugacity s) := by
  have hsre : s.re = (1 / 2 : ℝ) := hs
  unfold OnLeeYangCircle cayleyToFugacity
  rw [Complex.normSq_div]
  have hnorm : Complex.normSq s = Complex.normSq (1 - s) := by
    simp [Complex.normSq_apply]
    nlinarith [hsre]
  rw [hnorm]
  have hne : Complex.normSq (1 - s) ≠ 0 := by
    intro h
    have hz : (1 - s : ℂ) = 0 := Complex.normSq_eq_zero.mp h
    have hre0 : (1 - s).re = 0 := by
      rw [hz]
      simp
    simp at hre0
    nlinarith [hsre, hre0]
  field_simp [hne]

/--
The Cayley transform identifies the Riemann critical line with the Lee--Yang
unit circle.

This is the precise algebraic reformulation
`Re(s) = 1/2 ↔ |s / (1 - s)| = 1`, expressed through squared norm.
-/
theorem criticalLine_iff_cayley_unitCircle
    (s : ℂ) :
    OnCriticalLine s ↔ OnLeeYangCircle (cayleyToFugacity s) := by
  constructor
  · exact cayleyToFugacity_mem_unitCircle_of_criticalLine s
  · intro h
    unfold OnLeeYangCircle cayleyToFugacity at h
    rw [Complex.normSq_div] at h
    have hden : Complex.normSq (1 - s) ≠ 0 := by
      intro h0
      rw [h0] at h
      norm_num at h
    have hnorm : Complex.normSq s = Complex.normSq (1 - s) := by
      field_simp [hden] at h
      exact h
    unfold OnCriticalLine
    rw [Complex.normSq_apply, Complex.normSq_apply] at hnorm
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at hnorm
    nlinarith

theorem subset_cayley_unitCircle_iff_subset_criticalLine
    (Z : Set ℂ) :
    (∀ s ∈ Z, OnLeeYangCircle (cayleyToFugacity s)) ↔
      (∀ s ∈ Z, OnCriticalLine s) := by
  constructor
  · intro h s hs
    exact (criticalLine_iff_cayley_unitCircle s).2 (h s hs)
  · intro h s hs
    exact (criticalLine_iff_cayley_unitCircle s).1 (h s hs)

def cayleyImage (Z : Set ℂ) : Set ℂ :=
  cayleyToFugacity '' Z

theorem cayleyImage_subset_unitCircle_iff
    (Z : Set ℂ) :
    cayleyImage Z ⊆ {z | OnLeeYangCircle z} ↔
      Z ⊆ {s | OnCriticalLine s} := by
  constructor
  · intro h s hs
    exact (criticalLine_iff_cayley_unitCircle s).2
      (h ⟨s, hs, rfl⟩)
  · intro h z hz
    rcases hz with ⟨s, hs, rfl⟩
    exact (criticalLine_iff_cayley_unitCircle s).1 (h hs)

theorem cayleyImage_subset_unitCircleSet_iff
    (Z : Set ℂ) :
    cayleyImage Z ⊆ unitCircleSet ↔
      Z ⊆ criticalLineSet := by
  simpa [unitCircleSet, criticalLineSet] using
    (cayleyImage_subset_unitCircle_iff Z)

/-- The Lee--Yang unit circle condition is equivalent to the critical line after Cayley. -/
@[simp]
theorem cayleyToFugacity_mem_unitCircle_iff_criticalLine
    (s : ℂ) :
    OnLeeYangCircle (cayleyToFugacity s) ↔ OnCriticalLine s := by
  simpa using (criticalLine_iff_cayley_unitCircle s).symm

/--
The inverse Cayley transform maps the Lee--Yang unit circle back to the
critical line.

The property `z.re ≠ -1` excludes the point `z = -1`, where
`s = z / (1 + z)` is singular. On the unit circle this is the same excluded
endpoint of the Cayley chart.
-/
theorem cayleyToTemperature_mem_criticalLine_of_unitCircle
    (z : ℂ)
    (hz : OnLeeYangCircle z)
    (hre : z.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z) := by
  have hzs : Complex.normSq z = 1 := hz
  rw [Complex.normSq_apply] at hzs
  unfold OnCriticalLine cayleyToTemperature
  rw [Complex.div_re]
  have hnorm : Complex.normSq (1 + z) = 2 * (1 + z.re) := by
    simp [Complex.normSq_apply]
    nlinarith [hzs]
  have hnum : z.re * (1 + z.re) + z.im * z.im = 1 + z.re := by
    nlinarith [hzs]
  have hden : 2 * (1 + z.re) ≠ 0 := by
    intro h
    have : z.re = -1 := by
      linarith
    exact hre this
  have hden' : 1 + z.re ≠ 0 := by
    intro h
    have : z.re = -1 := by
      linarith
    exact hre this
  rw [hnorm]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
  have hcombine :
      z.re * (1 + z.re) / (2 * (1 + z.re)) +
          z.im * z.im / (2 * (1 + z.re)) =
        (z.re * (1 + z.re) + z.im * z.im) / (2 * (1 + z.re)) := by
    ring
  rw [hcombine, hnum]
  field_simp [hden, hden']

/--
The Riemann reflection `s ↦ 1 - s` becomes fugacity inversion.

This is the exact algebraic form of the UV/IR or particle-hole dictionary in
the Cayley coordinate.
-/
theorem cayleyToFugacity_one_sub_eq_inv
    (s : ℂ) :
    cayleyToFugacity (1 - s) = (cayleyToFugacity s)⁻¹ := by
  unfold cayleyToFugacity
  by_cases hs : s = 0
  · simp [hs]
  by_cases h1s : 1 - s = 0
  · simp [h1s]
  field_simp [hs, h1s]
  ring

/-! The inverse Cayley chart carries fugacity inversion back to reflection. -/
theorem cayleyToTemperature_inv_eq_one_sub
    {z : ℂ} (hz : z ≠ 0) (hz' : 1 + z ≠ 0) :
    cayleyToTemperature z⁻¹ = 1 - cayleyToTemperature z := by
  unfold cayleyToTemperature
  field_simp [hz, hz']
  have hden : z + 1 ≠ 0 := by simpa [add_comm] using hz'
  rw [show 1 + z = z + 1 by ring, div_self hden]
  ring

/-! The unit-circle condition is stable under fugacity inversion. -/
theorem onLeeYangCircle_inv
    {z : ℂ} (hz : OnLeeYangCircle z) :
    OnLeeYangCircle z⁻¹ := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num [OnLeeYangCircle] at hz
  unfold OnLeeYangCircle at hz ⊢
  rw [Complex.normSq_inv, hz]
  simp

/-! ## Prime-gas Lee--Yang approximation interface -/

/--
Finite-volume Lee--Yang approximation scheme for the completed
Riemann determinant in Cayley fugacity coordinates.

This records the exact missing theorem layer:

* each finite `Z N` is a genuine Lee--Yang polynomial;
* reciprocal symmetry must be proved in a concrete model;
* nonvanishing renormalization must be proved in a concrete model;
* convergence to the completed-`xi` Cayley readout is not asserted here;
* absence of spurious zeros is not asserted here;
* the final RH-style critical-line consequence is not stored as a field.

The structure deliberately stores only data and does not prove Lee--Yang
stability, Hurwitz zero convergence, analytic continuation of `xi`, or RH.
-/
structure LeeYangPrimeApproximation
    (CompletedXiReadout : Type*) where
  /-- Finite-volume prime-gas partition polynomial in fugacity coordinates. -/
  Z : ℕ → Polynomial ℂ
  /-- Renormalization factor for the finite-volume determinant readout. -/
  renormalization : ℕ → ℂ → ℂ
  /-- The completed `xi` readout in Cayley fugacity coordinates. -/
  completedXiCayley : CompletedXiReadout

end CayleyCriticalLineCircleBridge

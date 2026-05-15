import Mathlib

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

/--
The Cayley maps are inverse away from the pole `s = 1`.

Lean's field division is total, so the pole is recorded explicitly as a
hypothesis.
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
hypothesis.
-/
theorem cayleyToFugacity_cayleyToTemperature
    (z : ℂ)
    (hz : 1 + z ≠ 0) :
    cayleyToFugacity (cayleyToTemperature z) = z := by
  unfold cayleyToFugacity cayleyToTemperature
  field_simp [hz]
  ring

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
The inverse Cayley transform maps the Lee--Yang unit circle back to the
critical line.

The hypothesis `z.re ≠ -1` excludes the point `z = -1`, where
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

/-! ## Lee--Yang admissibility socket -/

/--
Witness-gated bridge from a Lee--Yang admissible determinant to an RH-style
critical-line statement through the Cayley transform.

The Lee--Yang circle theorem is not proved here. A concrete prime/Majorana
system must supply admissibility, the determinant identification with completed
`xi`, and the zero-location law.
-/
structure LeeYangCayleyRiemannWitness
    (PartitionFunction CompletedXiReadout ZeroReadout : Type*) where
  partitionFunction : PartitionFunction
  completedXiReadout : CompletedXiReadout
  zeroReadout : ZeroReadout
  leeYangAdmissible_law : Prop
  leeYangAdmissible_certificate :
    leeYangAdmissible_law
  cayleyDeterminant_eq_completedXi_law : Prop
  cayleyDeterminant_eq_completedXi_certificate :
    cayleyDeterminant_eq_completedXi_law
  zeros_on_unitCircle_law : Prop
  zeros_on_unitCircle_certificate :
    zeros_on_unitCircle_law
  cayley_unitCircle_zeros_imply_criticalLine_law : Prop
  cayley_unitCircle_zeros_imply_criticalLine_certificate :
    cayley_unitCircle_zeros_imply_criticalLine_law
  /-- Guardrail: this packet is not an unconditional proof of RH. -/
  no_unconditional_RH_claim_guard : Type*

namespace LeeYangCayleyRiemannWitness

/-- Re-export of the supplied Lee--Yang admissibility law. -/
theorem leeYangAdmissible
    {PartitionFunction CompletedXiReadout ZeroReadout : Type*}
    (W : LeeYangCayleyRiemannWitness
      PartitionFunction CompletedXiReadout ZeroReadout) :
    W.leeYangAdmissible_law :=
  W.leeYangAdmissible_certificate

/-- Re-export of the supplied completed-`xi` determinant identification. -/
theorem cayleyDeterminant_eq_completedXi
    {PartitionFunction CompletedXiReadout ZeroReadout : Type*}
    (W : LeeYangCayleyRiemannWitness
      PartitionFunction CompletedXiReadout ZeroReadout) :
    W.cayleyDeterminant_eq_completedXi_law :=
  W.cayleyDeterminant_eq_completedXi_certificate

/-- Re-export of the supplied unit-circle zero-location law. -/
theorem zeros_on_unitCircle
    {PartitionFunction CompletedXiReadout ZeroReadout : Type*}
    (W : LeeYangCayleyRiemannWitness
      PartitionFunction CompletedXiReadout ZeroReadout) :
    W.zeros_on_unitCircle_law :=
  W.zeros_on_unitCircle_certificate

/-- Re-export of the supplied Cayley/Riemann critical-line implication. -/
theorem cayley_unitCircle_zeros_imply_criticalLine
    {PartitionFunction CompletedXiReadout ZeroReadout : Type*}
    (W : LeeYangCayleyRiemannWitness
      PartitionFunction CompletedXiReadout ZeroReadout) :
    W.cayley_unitCircle_zeros_imply_criticalLine_law :=
  W.cayley_unitCircle_zeros_imply_criticalLine_certificate

end LeeYangCayleyRiemannWitness

end InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

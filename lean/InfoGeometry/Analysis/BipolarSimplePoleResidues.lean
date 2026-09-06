import InfoGeometry.Analysis.BipolarLogDifferential
import Mathlib.Tactic

/-!
# Genuine simple-pole coefficients of the bipolar logarithmic form

For a scalar meromorphic coefficient `f`, the residue at a certified simple
pole `a` is characterized by the punctured-neighbourhood limit

`(z-a) f(z) → r`.

This file proves that limit directly for the bipolar logarithmic coefficient

`dlog01(z)=1/z+1/(1-z)`.

The coefficients are `+1` at `0` and `-1` at `1`.  Unlike a declaration of a
constant pair, these theorems certify the actual local analytic limits.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarSimplePoleResidues

open Filter
open scoped Topology
open InfoGeometry.Analysis.BipolarLogDifferential

/-- Limit-based simple-pole coefficient predicate. -/
def HasSimplePoleCoefficientAt
    (f : ℂ → ℂ) (a residue : ℂ) : Prop :=
  Tendsto (fun z => (z - a) * f z) (𝓝[≠] a) (𝓝 residue)

/-- The origin regularization tends to `1`. -/
theorem dlog01_residue_zero_tendsto :
    Tendsto (fun z : ℂ => z * dlog01 z)
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
  have hid : Tendsto (fun z : ℂ => z)
      (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
    continuousAt_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun z : ℂ => 1 - z)
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using
      (tendsto_const_nhds.sub hid :
        Tendsto (fun z : ℂ => 1 - z)
          (𝓝[≠] (0 : ℂ)) (𝓝 ((1 : ℂ) - 0)))
  have hquot : Tendsto (fun z : ℂ => z / (1 - z))
      (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa using hid.div hden one_ne_zero
  have hregular : Tendsto (fun z : ℂ => 1 + z / (1 - z))
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using tendsto_const_nhds.add hquot
  apply hregular.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  simp [dlog01, div_eq_mul_inv, mul_add, hz0]

/-- The puncture at `0` has genuine simple-pole coefficient `+1`. -/
theorem dlog01_hasSimplePoleCoefficientAt_zero :
    HasSimplePoleCoefficientAt dlog01 0 1 := by
  simpa [HasSimplePoleCoefficientAt] using
    dlog01_residue_zero_tendsto

/-- The puncture-one regularization tends to `-1`. -/
theorem dlog01_residue_one_tendsto :
    Tendsto (fun z : ℂ => (z - 1) * dlog01 z)
      (𝓝[≠] (1 : ℂ)) (𝓝 (-1 : ℂ)) := by
  have hid : Tendsto (fun z : ℂ => z)
      (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) :=
    continuousAt_id.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun z : ℂ => z - 1)
      (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa using
      (hid.sub tendsto_const_nhds :
        Tendsto (fun z : ℂ => z - 1)
          (𝓝[≠] (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)))
  have hquot : Tendsto (fun z : ℂ => (z - 1) / z)
      (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa using hnum.div hid one_ne_zero
  have hregular : Tendsto (fun z : ℂ => (z - 1) / z - 1)
      (𝓝[≠] (1 : ℂ)) (𝓝 (-1 : ℂ)) := by
    simpa using hquot.sub tendsto_const_nhds
  apply hregular.congr'
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num))] with z hz hz0
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
  have hinv : (1 - z)⁻¹ = -(z - 1)⁻¹ := by
    rw [show 1 - z = -(z - 1) by ring, inv_neg]
  simp only [dlog01, div_eq_mul_inv, mul_add]
  rw [hinv]
  field_simp [hz0, hz1]
  ring

/-- The puncture at `1` has genuine simple-pole coefficient `-1`. -/
theorem dlog01_hasSimplePoleCoefficientAt_one :
    HasSimplePoleCoefficientAt dlog01 1 (-1) := by
  simpa [HasSimplePoleCoefficientAt] using
    dlog01_residue_one_tendsto

/-- The actual simple-pole coefficient pair is `(1,-1)`. -/
theorem dlog01_simplePoleCoefficient_pair :
    HasSimplePoleCoefficientAt dlog01 0 1 ∧
      HasSimplePoleCoefficientAt dlog01 1 (-1) := by
  exact ⟨dlog01_hasSimplePoleCoefficientAt_zero,
    dlog01_hasSimplePoleCoefficientAt_one⟩

/-- The two genuine simple-pole coefficients balance. -/
theorem dlog01_simplePoleCoefficient_sum_zero :
    (1 : ℂ) + (-1 : ℂ) = 0 := by
  ring

end InfoGeometry.Analysis.BipolarSimplePoleResidues

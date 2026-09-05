import InfoGeometry.Analysis.BipolarCayleyOccupation
import InfoGeometry.NCG.BerezinianSuperdeterminant

/-!
# Diagonal Berezinian, Cayley reciprocity, and the isolated midpoint pole

Over purely even complex scalars, an even automorphism of a `1|1` vector
space is diagonal. Its two diagonal entries must BOTH be units. The
Berezinian is the genuine group character `(a,d) |-> a/d` on `ℂˣ × ℂˣ`.

The total rational readout below reuses `berezinianBlockDiag`. It is a
Berezinian of `diag(1+z,1-z)` only where `z ≠ -1` AND `z ≠ 1`. A Lean value
at a zero denominator is not an analytic value at a pole.

The midpoint pole is not, by these identities alone, a Goldstone mode,
conformal anomaly, or collision of two sheets of a covering space.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarDiagonalBerezinianCayley

open Filter
open scoped Topology
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarCayleyOccupation
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Berezinian character of the actual even diagonal automorphism group. -/
def diagonalBerezinian : (ℂˣ × ℂˣ) →* ℂˣ where
  toFun p := p.1 * p.2⁻¹
  map_one' := by simp
  map_mul' p q := by
    change (p.1 * q.1) * (p.2 * q.2)⁻¹ =
      (p.1 * p.2⁻¹) * (q.1 * q.2⁻¹)
    rw [mul_inv_rev]
    ac_rfl

/-- The proposed diagonal pair is a group element only on this regular domain. -/
def fugacityDiagonalUnits (z : ℂ) (hplus : 1 + z ≠ 0) (hminus : 1 - z ≠ 0) :
    ℂˣ × ℂˣ :=
  (Units.mk0 (1 + z) hplus, Units.mk0 (1 - z) hminus)

/-- Native one-by-one block readout, using the repository determinant owner. -/
def fugacityBerezinianReadout (z : ℂ) : ℂ :=
  InfoGeometry.NCG.berezinianBlockDiag
    ((1 + z) • (1 : Matrix (Fin 1) (Fin 1) ℂ))
    ((1 - z) • (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (1 - z)⁻¹

/-- Exact scalar formula for the one-by-one block determinant ratio. -/
theorem fugacityBerezinianReadout_eq (z : ℂ) :
    fugacityBerezinianReadout z = (1 + z) / (1 - z) := by
  simp [fugacityBerezinianReadout, InfoGeometry.NCG.berezinianBlockDiag,
    Matrix.det_smul, div_eq_mul_inv]

/-- On the regular domain the rational readout equals the genuine unit-valued character. -/
theorem diagonalBerezinian_fugacity (z : ℂ)
    (hplus : 1 + z ≠ 0) (hminus : 1 - z ≠ 0) :
    (diagonalBerezinian (fugacityDiagonalUnits z hplus hminus) : ℂ) =
      fugacityBerezinianReadout z := by
  rw [fugacityBerezinianReadout_eq]
  rfl

/-- A unit-valued Berezinian never vanishes. -/
theorem diagonalBerezinian_ne_zero (p : ℂˣ × ℂˣ) :
    (diagonalBerezinian p : ℂ) ≠ 0 := (diagonalBerezinian p).ne_zero

/-- Exact rational identity; admissibility as a Berezinian is a separate theorem. -/
theorem fugacityBerezinianReadout_eq_neg_inv_cayley (z : ℂ) :
    fugacityBerezinianReadout z = -(fugacityCayley z)⁻¹ := by
  rw [fugacityBerezinianReadout_eq, fugacityCayley, inv_div]
  rw [show 1 - z = -(z - 1) by ring, div_neg]
  simp [add_comm]

/-- Centered rational readout in the original complex coordinate. -/
def centeredBerezinianReadout (s : ℂ) : ℂ := -(polarization s)⁻¹

/-- Pullback of the rational Berezinian readout to the existing cross-ratio chart. -/
theorem fugacityBerezinianReadout_crossRatio {s : ℂ} (hs : s ∈ punctured01) :
    fugacityBerezinianReadout (crossRatio01 s) = centeredBerezinianReadout s := by
  rw [fugacityBerezinianReadout_eq_neg_inv_cayley, fugacityCayley_crossRatio hs]
  rfl

/-- The odd block after the cross-ratio substitution. -/
theorem one_sub_crossRatio {s : ℂ} (hs : s ∈ punctured01) :
    1 - crossRatio01 s = -polarization s / (1 - s) := by
  unfold crossRatio01 cayleyToFugacity polarization
  field_simp [one_sub_ne_zero_of_mem hs]
  ring

/-- Its precise failure-of-invertibility locus is the single midpoint. -/
theorem odd_block_ne_zero_iff {s : ℂ} (hs : s ∈ punctured01) :
    1 - crossRatio01 s ≠ 0 ↔ s ≠ 1 / 2 := by
  rw [one_sub_crossRatio hs]
  simp only [ne_eq, div_eq_zero_iff, neg_eq_zero,
    one_sub_ne_zero_of_mem hs, or_false, polarization_eq_zero_iff]

/-- Both blocks are invertible everywhere on the chart except the midpoint. -/
theorem diagonal_blocks_regular {s : ℂ} (hs : s ∈ punctured01)
    (hmid : s ≠ 1 / 2) :
    1 + crossRatio01 s ≠ 0 ∧ 1 - crossRatio01 s ≠ 0 := by
  exact ⟨by simpa [add_comm] using crossRatio_add_one_ne_zero hs,
    (odd_block_ne_zero_iff hs).2 hmid⟩

/-- Berezinian/Cayley/tanh reciprocity for a genuine regular diagonal automorphism. -/
theorem diagonalBerezinian_exp (W : ℂ)
    (hplus : 1 + Complex.exp W ≠ 0) (hminus : 1 - Complex.exp W ≠ 0) :
    (diagonalBerezinian (fugacityDiagonalUnits (Complex.exp W) hplus hminus) : ℂ) =
      -(Complex.tanh (W / 2))⁻¹ := by
  rw [diagonalBerezinian_fugacity,
    fugacityBerezinianReadout_eq_neg_inv_cayley,
    fugacityCayley_exp W (by simpa [add_comm] using hplus)]

/-- The exact simple-pole coefficient in the original `s` coordinate is `-1/2`. -/
theorem centeredBerezinian_pole_coefficient {s : ℂ} (hs : s ≠ 1 / 2) :
    (s - 1 / 2) * centeredBerezinianReadout s = -1 / 2 := by
  have hp : polarization s ≠ 0 := by rwa [polarization_eq_zero_iff]
  have hd : 2 * s - 1 ≠ 0 := hp
  unfold centeredBerezinianReadout polarization
  field_simp [hd]
  ring

/-- A genuine punctured-neighborhood limit, not a totalized division value. -/
theorem centeredBerezinian_simple_pole :
    Tendsto (fun s : ℂ => (s - 1 / 2) * centeredBerezinianReadout s)
      (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (-1 / 2 : ℂ)) := by
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact centeredBerezinian_pole_coefficient (by simpa using hs)

/-- Away from the midpoint the critical-line readout is finite and purely imaginary. -/
theorem centeredBerezinian_criticalLine {y : ℝ} (hy : y ≠ 0) :
    centeredBerezinianReadout (criticalLine y) = Complex.I / (2 * (y : ℂ)) := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  rw [centeredBerezinianReadout, polarization_criticalLine]
  push_cast
  field_simp [hyc, Complex.I_ne_zero] <;>
    simp [Complex.I_sq] <;> ring

/-- The entire critical line is not a pole locus: every nonzero height is regular. -/
theorem criticalLine_odd_block_regular {y : ℝ} (hy : y ≠ 0) :
    1 - crossRatio01 (criticalLine y) ≠ 0 := by
  apply (odd_block_ne_zero_iff (criticalLine_mem_punctured01 y)).2
  intro h
  have hi := congrArg Complex.im h
  apply hy
  simpa using hi

/-- At the midpoint the proposed odd block is zero, hence is not a unit. -/
theorem midpoint_odd_block_not_unit :
    ¬ IsUnit (1 - crossRatio01 (criticalLine 0)) := by
  norm_num [crossRatio01, cayleyToFugacity, criticalLine]

end InfoGeometry.Canonical.BipolarDiagonalBerezinianCayley

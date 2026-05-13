/-
InfoGeometry/Canonical/WeylEntropyShiftBridge.lean

Logarithmic Weyl shift for positive homogeneous readouts.

This file does not assert that every Weyl-homogeneous readout is an entropy.
It packages the additional positivity needed to take a logarithm and proves the
standard additive shift forced by multiplicative Weyl homogeneity.
-/

import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.Meta.Architecture
import Mathlib

namespace InfoGeometry.Canonical.WeylEntropyShiftBridge

open InfoGeometry.Canonical.WeylHomogeneousReadoutBridge

/--
A positive Weyl-homogeneous partition/readout with logarithmic entropy readout.

The homogeneous readout supplies

  Z(scale c A) = c^w Z(A).

The positivity field supplies the domain needed for the entropy/log readout.
-/
@[rep_depth operator]
structure WeylHomogeneousEntropy (Op : Type*) where
  homogeneous : WeylHomogeneousOperatorReadout Op
  readout_pos : ∀ A, 0 < homogeneous.readout A

namespace WeylHomogeneousEntropy

variable {Op : Type*}
variable (W : WeylHomogeneousEntropy Op)

/-- Entropy/log readout of the positive homogeneous partition. -/
@[rep_depth operator]
noncomputable def entropy (A : Op) : ℝ :=
  Real.log (W.homogeneous.readout A)

/-- Direct readback of the partition/readout scaling law. -/
@[rep_depth operator]
theorem readout_scale
    (c : ℝ)
    (A : Op) :
    W.homogeneous.readout (W.homogeneous.scale c A) =
      c ^ W.homogeneous.weight * W.homogeneous.readout A :=
  W.homogeneous.scale_law c A

/--
Logarithmic Weyl shift.

For nonzero scale `c`, multiplicative homogeneity of weight `w` becomes the
additive entropy shift `w log c`.
-/
@[rep_depth operator]
theorem entropy_scale_shift
    (c : ℝ)
    (A : Op)
    (hc : c ≠ 0) :
    W.entropy (W.homogeneous.scale c A) =
      W.entropy A + W.homogeneous.weight * Real.log c := by
  unfold entropy
  calc
    Real.log (W.homogeneous.readout (W.homogeneous.scale c A))
        = Real.log (c ^ W.homogeneous.weight * W.homogeneous.readout A) := by
            rw [W.homogeneous.scale_law]
    _ = Real.log (c ^ W.homogeneous.weight) +
          Real.log (W.homogeneous.readout A) := by
            rw [Real.log_mul (pow_ne_zero W.homogeneous.weight hc)
              (ne_of_gt (W.readout_pos A))]
    _ = W.homogeneous.weight * Real.log c +
          Real.log (W.homogeneous.readout A) := by
            rw [Real.log_pow]
    _ = Real.log (W.homogeneous.readout A) +
          W.homogeneous.weight * Real.log c := by
            ring

/-- Positive-scale specialization of the logarithmic Weyl shift. -/
@[rep_depth operator]
theorem entropy_scale_shift_of_pos
    (c : ℝ)
    (A : Op)
    (hc : 0 < c) :
    W.entropy (W.homogeneous.scale c A) =
      W.entropy A + W.homogeneous.weight * Real.log c :=
  W.entropy_scale_shift c A (ne_of_gt hc)

/-- Weight-zero entropy readouts are scale-invariant under nonzero Weyl scaling. -/
@[rep_depth operator]
theorem entropy_scale_of_weight_zero
    (hW : W.homogeneous.weight = 0)
    (c : ℝ)
    (A : Op)
    (hc : c ≠ 0) :
    W.entropy (W.homogeneous.scale c A) = W.entropy A := by
  rw [W.entropy_scale_shift c A hc, hW]
  simp

/-- Weight-one entropy readouts shift by `log c`. -/
@[rep_depth operator]
theorem entropy_scale_of_weight_one
    (hW : W.homogeneous.weight = 1)
    (c : ℝ)
    (A : Op)
    (hc : c ≠ 0) :
    W.entropy (W.homogeneous.scale c A) = W.entropy A + Real.log c := by
  rw [W.entropy_scale_shift c A hc, hW]
  simp

/-- Weight-two entropy readouts shift by `2 log c`. -/
@[rep_depth operator]
theorem entropy_scale_of_weight_two
    (hW : W.homogeneous.weight = 2)
    (c : ℝ)
    (A : Op)
    (hc : c ≠ 0) :
    W.entropy (W.homogeneous.scale c A) = W.entropy A + 2 * Real.log c := by
  rw [W.entropy_scale_shift c A hc, hW]
  norm_num

end WeylHomogeneousEntropy

end InfoGeometry.Canonical.WeylEntropyShiftBridge


/-
InfoGeometry/Canonical/WeylHomogeneousReadoutBridge.lean

Generic Weyl-homogeneous readout bridge.

The arithmetic/projective owner lane is `InfoGeometry.Arithmetic.ProjectiveWeylGauge`.
This file does not redefine that scale/shape theory.  It supplies a small
operator/readout-facing carrier for layers whose physical scalar readout is
homogeneous under a Weyl scaling action.  Homogeneity laws are theorem-owner
surfaces below, not proof fields.
-/

import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Meta.Architecture
import Mathlib

namespace InfoGeometry.Canonical.WeylHomogeneousReadoutBridge

/--
A scalar readout with explicit Weyl weight.

`scale c A` is the homogeneous representative obtained by Weyl scaling `A`.
The law says the readout has weight `weight`.
-/
@[rep_depth operator]
structure WeylHomogeneousOperatorReadout (Op : Type*) where
  readout : Op → ℝ
  scale : ℝ → Op → Op
  weight : ℕ
  /-- The explicit homogeneity law for the readout. -/
  readout_scale_law :
    ∀ c A, readout (scale c A) = c ^ weight * readout A

namespace WeylHomogeneousOperatorReadout

variable {Op : Type*}
variable (W : WeylHomogeneousOperatorReadout Op)

/-- Direct readback of the Weyl homogeneity law. -/
@[rep_depth operator]
theorem readout_scale :
    ∀ c A, W.readout (W.scale c A) = c ^ W.weight * W.readout A :=
  W.readout_scale_law

/-- Weight-zero readouts are scale-invariant. -/
@[rep_depth operator]
theorem readout_scale_of_weight_zero
    (hW : W.weight = 0)
    (c : ℝ)
    (A : Op) :
    W.readout (W.scale c A) = W.readout A := by
  rw [W.readout_scale, hW]
  simp

/-- Weight-one readouts scale linearly. -/
@[rep_depth operator]
theorem readout_scale_of_weight_one
    (hW : W.weight = 1)
    (c : ℝ)
    (A : Op) :
    W.readout (W.scale c A) = c * W.readout A := by
  rw [W.readout_scale, hW]
  simp

/-- Weight-two readouts scale quadratically. -/
@[rep_depth operator]
theorem readout_scale_of_weight_two
    (hW : W.weight = 2)
    (c : ℝ)
    (A : Op) :
    W.readout (W.scale c A) = c ^ 2 * W.readout A := by
  rw [W.readout_scale, hW]

end WeylHomogeneousOperatorReadout

/--
A scale-invariant projective shape readout.

This is the operator/readout analogue of the projective shape lane: scaling a
homogeneous representative does not change the shape readout.
-/
@[rep_depth operator]
structure WeylInvariantShapeReadout (Op Shape : Type*) where
  shape : Op → Shape
  scale : ℝ → Op → Op
  /-- The explicit scale-invariance law for the projective shape. -/
  shape_scale_law :
    ∀ c A, c ≠ 0 → shape (scale c A) = shape A

namespace WeylInvariantShapeReadout

variable {Op Shape : Type*}
variable (S : WeylInvariantShapeReadout Op Shape)

/-- Direct readback of scale invariance for the projective shape. -/
@[rep_depth operator]
theorem shape_scale
    (c : ℝ)
    (A : Op)
    (hc : c ≠ 0) :
    S.shape (S.scale c A) = S.shape A :=
  S.shape_scale_law c A hc

end WeylInvariantShapeReadout

/--
Physical readout factorization:

  physical = Weyl scale ^ weight * projective invariant.

This records only the carrier data needed by volume, mass, entropy-shift, or
modular-energy layers.  Concrete readout owners must prove the factorization
law as a theorem.
-/
@[rep_depth operator]
structure WeylPhysicalReadoutFactorization (Op Shape : Type*) where
  physicalReadout : Op → ℝ
  shapeReadout : Shape → ℝ
  shape : Op → Shape
  scaleFactor : Op → ℝ
  weight : ℕ
  /-- The explicit factorization law for the physical readout. -/
  physicalReadout_factorization :
    ∀ A, physicalReadout A = scaleFactor A ^ weight * shapeReadout (shape A)

namespace WeylPhysicalReadoutFactorization

variable {Op Shape : Type*}
variable (F : WeylPhysicalReadoutFactorization Op Shape)

/-- Direct readback of the physical readout as Weyl scale to weight times shape core. -/
@[rep_depth operator]
theorem physical_eq_scale_pow_mul_shape
    (A : Op) :
    F.physicalReadout A =
      F.scaleFactor A ^ F.weight * F.shapeReadout (F.shape A) :=
  F.physicalReadout_factorization A

end WeylPhysicalReadoutFactorization

/--
The count/projective Weyl owner surface is imported explicitly.

This alias makes the dependency direction visible: operator physical readouts
should consume Weyl scale/shape data; they should not silently normalize away
the homogeneous representative.
-/
abbrev ArithmeticProjectiveWeylGaugeCalibration :=
  InfoGeometry.Arithmetic.ProjectiveWeylGauge.ProjectiveWeylGaugeCalibration

end InfoGeometry.Canonical.WeylHomogeneousReadoutBridge

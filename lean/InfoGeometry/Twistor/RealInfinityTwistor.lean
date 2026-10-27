/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealPluckerCl55Reflection

/-!
# The intrinsically real infinity form and its native Clifford readout

The infinity twistor is an actual linear map to the algebraic dual of the
real spinor-pair carrier. It is alternating and degenerate, with an explicit
radical and nonzero witness. Its value equals the existing `p23` minor and
the anticommutator readout after the native split-Klein embedding.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealInfinityTwistor

open RealTwistorIncidence RealTwistorSoldering RealTwistorBlockInversion
open RealPluckerCl55Reflection
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55InfinityWittBoundary

/-- The degenerate alternating form, as an operator to the genuine real dual. -/
def infinityTwistor : TwistorSpace →ₗ[ℝ] Module.Dual ℝ TwistorSpace where
  toFun z :=
    { toFun := fun w => z.2 0 * w.2 1 - z.2 1 * w.2 0
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  map_add' z w := by
    apply LinearMap.ext
    intro u
    simp
    ring
  map_smul' a z := by
    apply LinearMap.ext
    intro u
    simp
    ring

@[simp] theorem infinityTwistor_apply (z w : TwistorSpace) :
    infinityTwistor z w = z.2 0 * w.2 1 - z.2 1 * w.2 0 := rfl

theorem infinityTwistor_alternating (z : TwistorSpace) : infinityTwistor z z = 0 := by
  simp only [infinityTwistor_apply]
  ring

theorem infinityTwistor_skew (z w : TwistorSpace) :
    infinityTwistor z w = -infinityTwistor w z := by
  simp only [infinityTwistor_apply]
  ring

/-- The infinity readout is precisely the lower-spinor Plucker minor. -/
theorem infinityTwistor_eq_p23 (z w : TwistorSpace) :
    infinityTwistor z w = (twistorPlucker z w).p23 := rfl

/-- The radical is the whole upper-spinor plane, not merely the zero vector. -/
theorem infinityTwistor_radical (z : TwistorSpace) :
    infinityTwistor z = 0 ↔ z.2 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun f : Module.Dual ℝ TwistorSpace => f (0, ![0, 1])) h
    have h1 := congrArg (fun f : Module.Dual ℝ TwistorSpace => f (0, ![1, 0])) h
    simp only [infinityTwistor_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, mul_zero, sub_zero, zero_sub,
      LinearMap.zero_apply, neg_eq_zero] at h0 h1
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro h
    apply LinearMap.ext
    intro w
    simp [h]

theorem infinityTwistor_nonzero : infinityTwistor ≠ 0 := by
  intro h
  have hv := congrArg (fun A : TwistorSpace →ₗ[ℝ] Module.Dual ℝ TwistorSpace =>
    A (0, ![1, 0]) (0, ![0, 1])) h
  norm_num at hv

theorem infinityTwistor_not_injective : ¬ Function.Injective infinityTwistor := by
  intro h
  have hz : infinityTwistor ((![1, 0], 0) : TwistorSpace) = infinityTwistor 0 := by
    rw [map_zero]
    exact (infinityTwistor_radical _).mpr rfl
  have hcoord := congrArg (fun z : TwistorSpace => z.1 0) (h hz)
  norm_num at hcoord

/-- Translations preserve the lower-spinor pairing exactly. -/
theorem infinityTwistor_translation (d : Module.End ℝ Spinor) (z w : TwistorSpace) :
    infinityTwistor (translation d z) (translation d w) = infinityTwistor z w := rfl

/-- The real block rotation exchanges the infinity and origin pairings. -/
theorem infinityTwistor_blockRotation (z w : TwistorSpace) :
    infinityTwistor (blockRotation z) (blockRotation w) =
      (twistorPlucker z w).p01 := by
  simp only [infinityTwistor_apply, blockRotation_apply, Pi.neg_apply,
    twistorPlucker, twistorCoordinates, Plucker6.pluckerLine]
  ring

/-- The native anticommutator realizes this very same real dual pairing. -/
theorem infinityTwistor_native_readout (z w : TwistorSpace) :
    infinityClifford55 * ι55 (pluckerToV55 (twistorPlucker z w)) +
        ι55 (pluckerToV55 (twistorPlucker z w)) * infinityClifford55 =
      algebraMap ℝ Cl55 (infinityTwistor z w) := by
  rw [native_infinity_reads_p23, infinityTwistor_eq_p23]

/-- Rotation of the actual two twistors agrees with the native Clifford automorphism. -/
theorem twistor_native_reflection_intertwiner (z w : TwistorSpace) :
    partialReflectionAlg (ι55 (pluckerToV55 (twistorPlucker z w))) =
      ι55 (pluckerToV55 (twistorPlucker (blockRotation z) (blockRotation w))) := by
  rw [native_reflection_intertwiner, twistorPlucker_blockRotation]

end InfoGeometry.Twistor.RealInfinityTwistor

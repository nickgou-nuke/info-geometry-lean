/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RotorWeightOrbitBridge

/-! Algebraic Peirce compression of the existing rotor observable.
No positivity, normalized state, or analytic KMS assertion is made. -/
namespace InfoGeometry.Canonical.RotorPeirceWeightCompression
open DeBruijnRotorAlternationCycle
open GrassmannianBundleCyclotomicOrientability (normalBundlePart)
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

lemma normal_polePlus {d B : A} (h : IsDualSeedPair d B) :
    normalBundlePart (polePlus d B) (polePlus d B) = polePlus d B := by
  unfold normalBundlePart
  noncomm_ring [polePlus_idem h]

lemma normal_poleMinus {d B : A} (h : IsDualSeedPair d B) :
    normalBundlePart (polePlus d B) (poleMinus d B) = poleMinus d B := by
  unfold normalBundlePart
  noncomm_ring [polePlus_mul_poleMinus h, poleMinus_mul_polePlus h]

lemma normal_velocity {d B : A} (h : IsDualSeedPair d B) :
    normalBundlePart (polePlus d B) (transitionVelocity d B) = 0 := by
  have hz : polePlus d B * transitionVelocity d B * polePlus d B = 0 := by
    rw [polePlus_mul_velocity h]
    unfold polePlus
    rw [← mul_assoc, h.d_sq, zero_mul]
  unfold normalBundlePart
  calc
    _ = transitionVelocity d B - polePlus d B * transitionVelocity d B -
        transitionVelocity d B * polePlus d B +
        2 • (polePlus d B * transitionVelocity d B * polePlus d B) := by
          rw [two_nsmul]; noncomm_ring
    _ = 0 := by rw [hz, polePlus_mul_velocity h, velocity_mul_polePlus h]
                simp only [smul_zero, add_zero, transitionVelocity]; abel

/-- The normal Peirce projection is linear in its observable. -/
lemma normal_linear_combination (P X Y Z : A) (a b c : R) :
    normalBundlePart P (a • X + b • Y - c • Z) =
      a • normalBundlePart P X + b • normalBundlePart P Y -
      c • normalBundlePart P Z := by
  unfold normalBundlePart
  generalize (1 - P) = K
  simp only [mul_sub, sub_mul, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, smul_add]
  abel

/-- Compressing the existing elliptic orbit gives the existing squared weight.
The equation holds without a circle normalization hypothesis. -/
theorem normal_movingPolePlus_eq_weight {d B : A} (h : IsDualSeedPair d B)
    (c s : R) :
    normalBundlePart (polePlus d B) (movingPolePlus c s d B) =
      UnifiedGeometryOperatorSignificance.kmsModularWeight s c d B := by
  rw [movingPolePlus_eq h c s, normal_linear_combination,
    normal_polePlus h, normal_poleMinus h, normal_velocity h, smul_zero, sub_zero]
  change (c*c) • (d*B) + (s*s) • (B*d) = (s*s) • (B*d) + (c*c) • (d*B)
  exact add_comm _ _

/-- Exact remaining off-diagonal component of the native moving pole. -/
theorem movingPolePlus_sub_normal {d B : A} (h : IsDualSeedPair d B)
    (c s : R) :
    movingPolePlus c s d B - normalBundlePart (polePlus d B) (movingPolePlus c s d B) =
      -(c*s) • transitionVelocity d B := by
  rw [normal_movingPolePlus_eq_weight h c s, movingPolePlus_eq h c s]
  change (c*c) • (d*B) + (s*s) • (B*d) - (c*s) • (d+B) -
    ((s*s) • (B*d) + (c*c) • (d*B)) = -(c*s) • (d+B)
  rw [neg_smul]
  abel

end InfoGeometry.Canonical.RotorPeirceWeightCompression

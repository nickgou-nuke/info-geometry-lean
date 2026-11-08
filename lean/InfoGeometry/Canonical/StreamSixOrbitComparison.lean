/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ComplementHyperbolicOrbit
import InfoGeometry.Canonical.RotorPeirceWeightCompression
import InfoGeometry.Canonical.HyperbolicEllipticKmsDecoherence

/-! Algebraic comparison on the same native seed pair and active carrier.
The conjugation and polynomial owners are identified explicitly.
No metric, positivity, analytic KMS, or aggregate certificate is asserted. -/
namespace InfoGeometry.Canonical.StreamSixOrbitComparison

open DeBruijnRotorAlternationCycle
open ComplementHyperbolicOrbit (hyperbolicPlus hyperbolicMinus)
open GrassmannianBundleCyclotomicOrientability (normalBundlePart)

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Actual hyperbolic conjugation realizes the existing Stream6 plus polynomial. -/
theorem hyperbolicPlus_eq_stream6 {d B : A} (h : IsDualSeedPair d B) (u v : R) :
    hyperbolicPlus u v d B =
      HyperbolicEllipticKmsDecoherence.hyperbolicPolePlus u v d B := by
  exact ComplementHyperbolicOrbit.hyperbolicPlus_expansion h u v

/-- The opposite conjugated pole realizes the existing polynomial with its ordering. -/
theorem hyperbolicMinus_eq_stream6 {d B : A} (h : IsDualSeedPair d B) (u v : R) :
    hyperbolicMinus u v d B =
      HyperbolicEllipticKmsDecoherence.hyperbolicPoleMinus u v d B := by
  rw [ComplementHyperbolicOrbit.hyperbolicMinus_expansion h u v]
  change (u*u) • (B*d) - (v*v) • (d*B) + (u*v) • (d-B) =
    -(v*v) • (d*B) + (u*u) • (B*d) + (u*v) • (d-B)
  rw [neg_smul]
  abel

/-- The full normal corner and active diagonal agree on this supported observable. -/
theorem normal_movingPolePlus_eq_diagonal {d B : A} (h : IsDualSeedPair d B)
    (c s : R) :
    normalBundlePart (polePlus d B) (movingPolePlus c s d B) =
      HyperbolicEllipticKmsDecoherence.diagonalDecoherence d B
        (movingPolePlus c s d B) := by
  have h6 := (HyperbolicEllipticKmsDecoherence.isDualSeedPair_iff_stream5 d B).mpr h
  have he := (HyperbolicEllipticKmsDecoherence.stream6_stream3_stream5_coherence
    h6 c s).2
  rw [RotorPeirceWeightCompression.normal_movingPolePlus_eq_weight h c s, he,
    HyperbolicEllipticKmsDecoherence.diagonalDecoherence_ellipticPolePlus_eq_kms h6 c s]
  rfl

/-- The opposite algebraic displacement signs combine on the same active support. -/
theorem displacement_squares_add {d B : A} (h : IsDualSeedPair d B)
    (c s u v : R) (hc : c*c+s*s=1) (hu : u*u-v*v=1) :
    (movingPolePlus c s d B - polePlus d B) *
        (movingPolePlus c s d B - polePlus d B) +
      (hyperbolicPlus u v d B - polePlus d B) *
        (hyperbolicPlus u v d B - polePlus d B) =
      (s*s-v*v) • carrierSupport d B := by
  have hh := ComplementHyperbolicOrbit.hyperbolicPlus_displacement_square h u v hu
  change (hyperbolicPlus u v d B - polePlus d B) *
    (hyperbolicPlus u v d B - polePlus d B) = -((v*v) • carrierSupport d B) at hh
  rw [(movingPolePlus_chordal_square_and_compression h hc).1, hh,
    sub_smul, sub_eq_add_neg]

/-- Difference of compressions; the hyperbolic parameters need no normalization. -/
theorem compression_sub {d B : A} (h : IsDualSeedPair d B)
    (c s u v : R) (hc : c*c+s*s=1) :
    polePlus d B * movingPolePlus c s d B * polePlus d B -
      polePlus d B * hyperbolicPlus u v d B * polePlus d B =
      (c*c-u*u) • polePlus d B := by
  have hh := ComplementHyperbolicOrbit.hyperbolicPlus_compression h u v
  change polePlus d B * hyperbolicPlus u v d B * polePlus d B =
    (u*u) • polePlus d B at hh
  rw [(movingPolePlus_chordal_square_and_compression h hc).2, hh, sub_smul]

end InfoGeometry.Canonical.StreamSixOrbitComparison

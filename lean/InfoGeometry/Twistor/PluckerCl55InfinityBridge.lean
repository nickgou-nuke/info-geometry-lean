/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.InfinityTwistor
import InfoGeometry.Twistor.PluckerLorentzRealForm
import InfoGeometry.Twistor.PluckerBlockInversion
import InfoGeometry.Canonical.Cl55InfinityWittBoundary

/-!
# The Lorentzian Klein slice and the native Clifford infinity pair

The existing real six-dimensional carrier embeds injectively into native
`V55`, with its two homogeneous coordinates on the distinguished Witt pair.
The native quadratic form restricts to `quadratic24`; its polar form is the
negative of the complex Klein polar form on this real slice. Consequently
the native infinity anticommutator reads the genuine Penrose infinity form
when an actual twistor pair represents a point of this slice.

This is an embedding into a larger quadratic carrier. The Plücker infinity
representative maps to minus the native infinity vector; this sign follows
from `kleinQ = -quadratic24`. No identification of the two Clifford algebras
or claim that all five grading sectors are nonzero is made here.
-/

noncomputable section

namespace InfoGeometry.Twistor.PluckerCl55InfinityBridge

open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open InfoGeometry.Bridge.ZornConformalSixCone
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorPlucker
open InfoGeometry.Twistor.InfinityTwistor
open InfoGeometry.Twistor.PluckerInfinityChart
open InfoGeometry.Twistor.PluckerLorentzRealForm
open InfoGeometry.Twistor.PluckerBlockInversion
open InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open InfoGeometry.Clifford.Clifford55
open ProjectiveAffineConformalClosure55

/-- Put the homogeneous coordinates on the owner's distinguished Witt pair. -/
def conformalSixToPAC55 (X : ConformalSix) : PACSplit55 where
  x0 := X.a0
  x1 := 0
  x2 := 0
  x3 := 0
  y0 := X.ax
  y1 := X.ay
  y2 := X.az
  y3 := 0
  u := X.bz
  v := X.b0

def conformalSixToV55 (X : ConformalSix) : V55 :=
  pacSplit55ToV55 (conformalSixToPAC55 X)

def v55ConformalReadback (v : V55) : ConformalSix where
  a0 := v.1 0
  ax := v.2 0
  ay := v.2 1
  az := v.2 2
  b0 := v.2 4
  bz := v.1 4

@[simp] theorem v55ConformalReadback_embedding (X : ConformalSix) :
    v55ConformalReadback (conformalSixToV55 X) = X := by
  cases X
  rfl

theorem conformalSixToV55_injective : Function.Injective conformalSixToV55 :=
  Function.LeftInverse.injective v55ConformalReadback_embedding

/-- Passing to native Clifford generators retains every real coordinate. -/
theorem native_generator_injective :
    Function.Injective (fun X : ConformalSix => ι55 (conformalSixToV55 X)) :=
  ι55_injective.comp conformalSixToV55_injective

theorem conformalSixToV55_scale (c : ℝ) (X : ConformalSix) :
    conformalSixToV55 (InfoGeometry.Bridge.ZornConformalSixCone.scale c X) =
      c • conformalSixToV55 X := by
  ext i <;> fin_cases i <;>
    simp [conformalSixToV55, conformalSixToPAC55, pacSplit55ToV55,
      InfoGeometry.Bridge.ZornConformalSixCone.scale]

theorem nativeQ55_conformalSixToV55 (X : ConformalSix) :
    InfoGeometry.Clifford.Clifford55.Q55 (conformalSixToV55 X) = quadratic24 X := by
  unfold conformalSixToV55
  rw [nativeQ55_pacSplit55ToV55]
  simp [ProjectiveAffineConformalClosure55.Q55, conformalSixToPAC55, quadratic24]

/-- This also fixes the normalization: neither polar form is divided by two. -/
theorem kleinPolar_eq_neg_nativePolar (X Y : ConformalSix) :
    kleinPolar (lorentzPlucker X) (lorentzPlucker Y) =
      -((QuadraticMap.polar InfoGeometry.Clifford.Clifford55.Q55
        (conformalSixToV55 X) (conformalSixToV55 Y) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [kleinPolar, lorentzPlucker, QuadraticMap.polar,
      InfoGeometry.Clifford.Clifford55.Q55_apply, conformalSixToV55,
      conformalSixToPAC55, pacSplit55ToV55, Fin.sum_univ_succ, pow_two] <;> ring

/-- The readback is an identity in the owner's noncommutative Clifford algebra. -/
theorem native_anticommutator_eq_kleinPolar (X Y : ConformalSix) :
    ι55 (conformalSixToV55 X) * ι55 (conformalSixToV55 Y) +
        ι55 (conformalSixToV55 Y) * ι55 (conformalSixToV55 X) =
      algebraMap ℝ Cl55 (-(kleinPolar (lorentzPlucker X) (lorentzPlucker Y)).re) := by
  rw [CliffordAlgebra.ι_mul_ι_add_swap, kleinPolar_eq_neg_nativePolar]
  simp

theorem native_null_iff_klein (X : ConformalSix) :
    InfoGeometry.Clifford.Clifford55.Q55 (conformalSixToV55 X) = 0 ↔
      kleinQ (lorentzPlucker X) = 0 := by
  rw [nativeQ55_conformalSixToV55, kleinQ_lorentzPlucker,
    neg_eq_zero, Complex.ofReal_eq_zero]

theorem native_klein_generator_sq_zero (X : ConformalSix)
    (hX : kleinQ (lorentzPlucker X) = 0) :
    ι55 (conformalSixToV55 X) * ι55 (conformalSixToV55 X) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, (native_null_iff_klein X).mpr hX]
  simp

theorem native_infinity_reads_p23 (X : ConformalSix) :
    infinityClifford55 * ι55 (conformalSixToV55 X) +
        ι55 (conformalSixToV55 X) * infinityClifford55 =
      algebraMap ℝ Cl55 (lorentzPlucker X).p23.re := by
  simpa [infinityClifford55, conformalSixToV55, affineGaugeCoord,
    conformalSixToPAC55, lorentzPlucker, add_comm] using
    infinity_reads_affineGauge (conformalSixToPAC55 X)

theorem native_origin_reads_neg_p01 (X : ConformalSix) :
    originClifford55 * ι55 (conformalSixToV55 X) +
        ι55 (conformalSixToV55 X) * originClifford55 =
      algebraMap ℝ Cl55 (-(lorentzPlucker X).p01.re) := by
  simpa [originClifford55, conformalSixToV55, complementaryGaugeCoord,
    conformalSixToPAC55, lorentzPlucker, neg_sub] using
    origin_reads_complementaryGauge (conformalSixToPAC55 X)

/-- The sign is required by the opposite quadratic-form conventions. -/
theorem native_image_infinityPlucker :
    conformalSixToV55 (lorentzReadback (infinityPlucker : Plucker6 ℂ)) =
      -infinityVector55 := by
  ext i <;> fin_cases i <;>
    norm_num [conformalSixToV55, conformalSixToPAC55, pacSplit55ToV55,
      lorentzReadback, infinityPlucker_coordinates, infinityVector55,
      n_bar_vec, nbar_pair, e_pos, f_neg]

theorem native_image_originPlucker :
    conformalSixToV55 (lorentzReadback (graphPlucker (0 : ComplexSpacetime))) =
      originVector55 := by
  ext i <;> fin_cases i <;>
    norm_num [conformalSixToV55, conformalSixToPAC55, pacSplit55ToV55,
      lorentzReadback, graphPlucker_coordinates, Matrix.det_fin_two,
      originVector55, n_vec, n_pair, e_pos, f_neg]

/-- The real-slice hypothesis prevents loss of an imaginary component. -/
theorem infinityTwistor_eq_native_affineGauge (Z W : Twistor4) (X : ConformalSix)
    (hX : twistorPairPlucker Z W = lorentzPlucker X) :
    infinityTwistor Z W = (affineGaugeCoord (conformalSixToPAC55 X) : ℂ) := by
  rw [infinityTwistor_eq_plucker_p23, hX]
  simp [lorentzPlucker, affineGaugeCoord, conformalSixToPAC55, add_comm]

theorem native_infinity_reads_infinityTwistor (Z W : Twistor4) (X : ConformalSix)
    (hX : twistorPairPlucker Z W = lorentzPlucker X) :
    infinityClifford55 * ι55 (conformalSixToV55 X) +
        ι55 (conformalSixToV55 X) * infinityClifford55 =
      algebraMap ℝ Cl55 (infinityTwistor Z W).re := by
  rw [infinityTwistor_eq_plucker_p23, hX]
  exact native_infinity_reads_p23 X

/-- On the real Klein image, the two actual boundary conditions are equivalent. -/
theorem native_infinity_zero_iff_infinityTwistor_zero
    (Z W : Twistor4) (X : ConformalSix)
    (hX : twistorPairPlucker Z W = lorentzPlucker X) :
    (infinityClifford55 * ι55 (conformalSixToV55 X) +
        ι55 (conformalSixToV55 X) * infinityClifford55 = 0) ↔
      infinityTwistor Z W = 0 := by
  rw [infinityTwistor_eq_native_affineGauge Z W X hX, Complex.ofReal_eq_zero]
  exact infinity_orthogonal_iff_affineGauge_zero (conformalSixToPAC55 X)

end InfoGeometry.Twistor.PluckerCl55InfinityBridge

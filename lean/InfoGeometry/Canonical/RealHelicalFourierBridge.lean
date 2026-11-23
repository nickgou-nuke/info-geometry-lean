/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.KMSShearTubuleKleinPrimonBridge
import InfoGeometry.Clifford.Cl55FiniteCommutingRotorAction
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Helical cover coordinates and real Fourier phase

The map `(u,t) ↦ (R cos(2πu), R sin(2πu), t-Pu)` is a periodic
parameterization. It is not injective on the plane. Its angular and axial
coordinates project to the native carrier `AddCircle 1 × ℝ`; only this
coordinate projection and its integer screw invariance are constructed here.

The affine seam reuses the existing glide reflection. A half screw shift
acts antipodally on the first two Cartesian coordinates and leaves the axial
coordinate unchanged. Two such shifts give one full angular period.

The real matrix mode uses the existing positive quarter-turn matrix and
generic rotor. Its angular frequency is an integer, while its axial frequency
is an arbitrary real number. The restricted two-integer mode is recovered by
`n = k + ω` and `ν = ω / P` when `P ≠ 0`. This is a phase identity, with no
topological bundle construction, spin representation, spectral quantization,
or assertion about zeros of an analytic function.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealHelicalFourierBridge

open InfoGeometry.Canonical.KMSShearTubuleKleinPrimon
open InfoGeometry.Clifford.FiniteCommutingRotorAction

/-- The axial coordinate unchanged by the screw identification. -/
def axialCoordinate (P u t : ℝ) : ℝ := t - P * u

/-- A periodic cylindrical cover parameterization in real Cartesian coordinates. -/
def tubuleCover (R P u t : ℝ) : ℝ × ℝ × ℝ :=
  (R * Real.cos (2 * Real.pi * u),
   R * Real.sin (2 * Real.pi * u), axialCoordinate P u t)

theorem axialCoordinate_screw (P u t : ℝ) (m : ℤ) :
    axialCoordinate P (u + m) (t + P * m) = axialCoordinate P u t := by
  unfold axialCoordinate
  ring

/-- The radius identity is inherited from the existing sheared-angle owner. -/
theorem tubuleCover_radius (R P u t : ℝ) :
    (tubuleCover R P u t).1 ^ 2 + (tubuleCover R P u t).2.1 ^ 2 = R ^ 2 := by
  simpa [tubuleCover, shearedAngle, pow_two] using
    helical_radius_sq R (2 * Real.pi) 0 0 u

theorem tubuleCover_screw (R P u t : ℝ) (m : ℤ) :
    tubuleCover R P (u + m) (t + P * m) = tubuleCover R P u t := by
  have hθ : 2 * Real.pi * (u + m) = 2 * Real.pi * u + m * (2 * Real.pi) := by
    ring
  simp only [tubuleCover, hθ, Real.cos_add_int_mul_two_pi,
    Real.sin_add_int_mul_two_pi, axialCoordinate_screw]

theorem tubuleCover_half_screw (R P u t : ℝ) :
    tubuleCover R P (u + 1 / 2) (t + P / 2) =
      (-(tubuleCover R P u t).1, -(tubuleCover R P u t).2.1,
        (tubuleCover R P u t).2.2) := by
  have hθ : 2 * Real.pi * (u + 1 / 2) = 2 * Real.pi * u + Real.pi := by
    ring
  have hz : axialCoordinate P (u + 1 / 2) (t + P / 2) =
      axialCoordinate P u t := by
    unfold axialCoordinate
    ring
  simp only [tubuleCover, hθ, Real.cos_add_pi, Real.sin_add_pi, mul_neg, hz]

/-- A nonzero deck displacement already prevents injectivity on the plane. -/
theorem tubuleCover_not_injective (R P : ℝ) :
    ¬Function.Injective (fun p : ℝ × ℝ => tubuleCover R P p.1 p.2) := by
  intro h
  have hperiod : tubuleCover R P 1 P = tubuleCover R P 0 0 := by
    simpa only [Int.cast_one, zero_add, mul_one] using tubuleCover_screw R P 0 0 1
  have hp : ((1 : ℝ), P) = ((0 : ℝ), 0) := h hperiod
  have hx := congrArg Prod.fst hp
  norm_num at hx

/-- The existing glide on `(σ,t)` is accompanied by an angular half shift. -/
def helicalSeam (P : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((glideReflection P (p.1, p.2.2)).1, p.2.1 + 1 / 2,
    (glideReflection P (p.1, p.2.2)).2)

theorem helicalSeam_sq (P : ℝ) (p : ℝ × ℝ × ℝ) :
    helicalSeam P (helicalSeam P p) = (p.1, p.2.1 + 1, p.2.2 + P) := by
  apply Prod.ext
  · exact congrArg Prod.fst (glide_squared P (p.1, p.2.2))
  · apply Prod.ext
    · change p.2.1 + 1 / 2 + 1 / 2 = p.2.1 + 1
      ring
    · exact congrArg Prod.snd (glide_squared P (p.1, p.2.2))

theorem helicalSeam_sq_cover (R P : ℝ) (p : ℝ × ℝ × ℝ) :
    tubuleCover R P (helicalSeam P (helicalSeam P p)).2.1
      (helicalSeam P (helicalSeam P p)).2.2 = tubuleCover R P p.2.1 p.2.2 := by
  rw [helicalSeam_sq]
  simpa only [Int.cast_one, mul_one] using tubuleCover_screw R P p.2.1 p.2.2 1

/-- This is the fixed locus of the reflection component, not of the full seam. -/
theorem helicalSeam_reflection_fixed_iff (P σ u t : ℝ) :
    (helicalSeam P (σ, u, t)).1 = σ ↔ σ = 1 / 2 :=
  glide_fixed_iff_midline σ

/-- The native angular quotient together with the unchanged real axial coordinate. -/
def cylinderCoordinate (P u t : ℝ) : AddCircle (1 : ℝ) × ℝ :=
  ((u : AddCircle (1 : ℝ)), axialCoordinate P u t)

theorem cylinderCoordinate_screw (P u t : ℝ) (m : ℤ) :
    cylinderCoordinate P (u + m) (t + P * m) = cylinderCoordinate P u t := by
  have hm : ((m : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
    exact ⟨m, by simp⟩
  apply Prod.ext
  · change ((u + m : ℝ) : AddCircle (1 : ℝ)) = (u : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add, hm, add_zero]
  · exact axialCoordinate_screw P u t m

/-- Real matrix Fourier phase with integer angular and unrestricted real axial frequency. -/
def helicalMode (n : ℤ) (ν P u t : ℝ) : M2R :=
  rotor atomJ (2 * Real.pi * ((n : ℝ) * u + ν * axialCoordinate P u t))

theorem helicalMode_add (n : ℤ) (ν P u t v s : ℝ) :
    helicalMode n ν P (u + v) (t + s) =
      helicalMode n ν P u t * helicalMode n ν P v s := by
  have hJ : atomJ * atomJ = -(1 : M2R) := by simpa using atomJ_sq
  unfold helicalMode
  rw [← rotor_add atomJ hJ]
  congr 1
  unfold axialCoordinate
  ring

theorem helicalMode_screw (n : ℤ) (ν P u t : ℝ) (m : ℤ) :
    helicalMode n ν P (u + m) (t + P * m) = helicalMode n ν P u t := by
  unfold helicalMode
  rw [axialCoordinate_screw]
  have hθ :
      2 * Real.pi * ((n : ℝ) * (u + m) + ν * axialCoordinate P u t) =
        2 * Real.pi * ((n : ℝ) * u + ν * axialCoordinate P u t) +
          ((n * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [hθ]
  simp only [rotor, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem helicalMode_half_screw (n : ℤ) (ν P u t : ℝ) :
    helicalMode n ν P (u + 1 / 2) (t + P / 2) =
      (-1 : ℝ) ^ n • helicalMode n ν P u t := by
  have hθ :
      2 * Real.pi * ((n : ℝ) * (u + 1 / 2) +
        ν * axialCoordinate P (u + 1 / 2) (t + P / 2)) =
      2 * Real.pi * ((n : ℝ) * u + ν * axialCoordinate P u t) + n * Real.pi := by
    unfold axialCoordinate
    ring
  simp only [helicalMode, hθ, rotor, Real.cos_add_int_mul_pi,
    Real.sin_add_int_mul_pi, smul_add, smul_smul]

theorem helicalMode_half_screw_parity (n : ℤ) (ν P u t : ℝ) :
    helicalMode n ν P (u + 1 / 2) (t + P / 2) =
      (if Even n then (1 : ℝ) else -1) • helicalMode n ν P u t := by
  rw [helicalMode_half_screw, neg_one_zpow_eq_ite]

/-- The attachment's restricted integer family, represented by the same real rotor. -/
def restrictedMode (k ω : ℤ) (P u t : ℝ) : M2R :=
  rotor atomJ (2 * Real.pi * ((k : ℝ) * u + (ω : ℝ) * (t / P)))

theorem restrictedMode_eq_helicalMode (k ω : ℤ) {P : ℝ} (hP : P ≠ 0) (u t : ℝ) :
    restrictedMode k ω P u t = helicalMode (k + ω) ((ω : ℝ) / P) P u t := by
  unfold restrictedMode helicalMode axialCoordinate
  congr 1
  push_cast
  field_simp [hP] <;> ring

theorem restrictedMode_half_screw_parity (k ω : ℤ) {P : ℝ} (hP : P ≠ 0) (u t : ℝ) :
    restrictedMode k ω P (u + 1 / 2) (t + P / 2) =
      (if Even (k + ω) then (1 : ℝ) else -1) • restrictedMode k ω P u t := by
  simp only [restrictedMode_eq_helicalMode k ω hP]
  exact helicalMode_half_screw_parity (k + ω) ((ω : ℝ) / P) P u t

end InfoGeometry.Canonical.RealHelicalFourierBridge

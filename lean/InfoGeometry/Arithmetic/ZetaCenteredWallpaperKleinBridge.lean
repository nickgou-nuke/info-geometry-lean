import Mathlib.Tactic

import InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Topology.WallpaperSymmetry

/-!
# Centered zeta coordinates and the native wallpaper Klein presentation

This file is only a coordinate transport layer.  It reuses the existing
centered zeta chart, the existing Cayley critical-circle theorem, and the
existing `pg` wallpaper action.

The two translations are kept distinct:

* the glide square is the horizontal translation `T_x`;
* the glide conjugates the transverse translation `T_y` to its inverse.

No quotient-space, manifold, Riemann-hypothesis, or Souriau moment-map claim
is made here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaCenteredWallpaperKleinBridge

open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Topology.Wallpaper

/-! ## Centered zeta to wallpaper coordinates -/

/-- The wallpaper dictionary is `(x_wall, y_wall) = (Im s, Re s - 1/2)`. -/
def zetaWallpaperCoordinate (z : ZetaAffineChart) : Lattice2D :=
  (z.tau, centeredSigma z)

@[simp]
theorem zetaWallpaperCoordinate_apply (z : ZetaAffineChart) :
    zetaWallpaperCoordinate z = (z.tau, centeredSigma z) :=
  rfl

theorem zetaWallpaperCoordinate_functionalDual (z : ZetaAffineChart) :
    zetaWallpaperCoordinate (chartFunctionalDual z) =
      ((-zetaWallpaperCoordinate z).1,
        (-zetaWallpaperCoordinate z).2) := by
  ext <;>
    simp [zetaWallpaperCoordinate, chartFunctionalDual, centeredSigma]
  <;> ring

theorem zetaWallpaperCoordinate_criticalMirror (z : ZetaAffineChart) :
    zetaWallpaperCoordinate (chartCriticalMirror z) =
      ((zetaWallpaperCoordinate z).1,
        -(zetaWallpaperCoordinate z).2) := by
  ext <;>
    simp [zetaWallpaperCoordinate, chartCriticalMirror, centeredSigma]
  <;> ring

theorem zetaWallpaperCoordinate_criticalLine_iff_second_eq_zero
    (z : ZetaAffineChart) :
    chartCriticalLine z ↔
      (zetaWallpaperCoordinate z).2 = 0 := by
  simpa [zetaWallpaperCoordinate, chartCriticalLine, centeredSigma] using
    (chartCriticalLine_iff_centeredSigma_eq_zero z)

/-! ## Existing wallpaper glide on the transported chart -/

/-- Apply the existing wallpaper glide to a centered zeta point. -/
def zetaWallpaperGlide (z : ZetaAffineChart) : Lattice2D :=
  G (zetaWallpaperCoordinate z)

theorem zetaWallpaperGlide_apply (z : ZetaAffineChart) :
    zetaWallpaperGlide z =
      (z.tau + (1 / 2 : ℝ), -centeredSigma z) := by
  ext <;> simp [zetaWallpaperGlide, zetaWallpaperCoordinate, G,
    centeredSigma]
  <;> ring

theorem zetaWallpaperGlide_square (z : ZetaAffineChart) :
    G (G (zetaWallpaperCoordinate z)) =
      T_x (zetaWallpaperCoordinate z) := by
  exact glide_squared_eq_x_translation (zetaWallpaperCoordinate z)

theorem zetaWallpaperGlide_conjugates_transverse (z : ZetaAffineChart) :
    G (T_y (G.symm (zetaWallpaperCoordinate z))) =
      T_y.symm (zetaWallpaperCoordinate z) := by
  simpa [concretePG] using
    concrete_pg_conjugates_y_translation_to_inverse
      (zetaWallpaperCoordinate z)

/-! ## Cayley readout reused from the canonical owner -/

theorem zeta_functional_reflection_cayley_inversion (s : ℂ) :
    cayleyToFugacity (functionalReflection s) =
      (cayleyToFugacity s)⁻¹ := by
  simpa [functionalReflection] using
    cayleyToFugacity_one_sub_eq_inv s

theorem zeta_criticalLine_cayley_unitCircle (s : ℂ) :
    OnCriticalLine s ↔
      OnLeeYangCircle (cayleyToFugacity s) :=
  criticalLine_iff_cayley_unitCircle s

theorem zeta_criticalMirror_fixed_iff (z : ZetaAffineChart) :
    chartCriticalMirror z = z ↔ chartCriticalLine z :=
  fixed_chartCriticalMirror_iff_criticalLine z

/-! ## Height Cayley compactification -/

/-- Cayley compactification of the real height coordinate. -/
def heightCayley (v : ℝ) : ℂ :=
  ((v : ℂ) - Complex.I) / ((v : ℂ) + Complex.I)

theorem heightCayley_normSq (v : ℝ) :
    Complex.normSq (heightCayley v) = 1 := by
  rw [heightCayley, Complex.normSq_div]
  simp [Complex.normSq]
  have hv : 0 < (1 + v ^ 2 : ℝ) := by positivity
  field_simp [ne_of_gt hv]
  all_goals nlinarith [sq_nonneg v]

theorem heightCayley_neg (v : ℝ) :
    heightCayley (-v) = (heightCayley v)⁻¹ := by
  unfold heightCayley
  rw [inv_div]
  have hnum : ((-v : ℂ) - Complex.I) = -((v : ℂ) + Complex.I) := by
    ring
  have hden : ((-v : ℂ) + Complex.I) = -((v : ℂ) - Complex.I) := by
    ring
  have hplus : ((v : ℂ) + Complex.I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hminus : ((v : ℂ) - Complex.I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hcast : ((-v : ℝ) : ℂ) = -(v : ℂ) := by
    norm_num
  rw [hcast]
  rw [hnum, hden]
  field_simp [hplus, hminus]

theorem heightCayley_norm (v : ℝ) :
    ‖heightCayley v‖ = 1 := by
  have h := heightCayley_normSq v
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg (heightCayley v)]

def zetaCylinderCoordinate (z : ZetaAffineChart) : ℝ × ℂ :=
  (centeredSigma z, heightCayley z.tau)

theorem zetaCylinderCoordinate_functionalDual (z : ZetaAffineChart) :
    zetaCylinderCoordinate (chartFunctionalDual z) =
      (-centeredSigma z, (heightCayley z.tau)⁻¹) := by
  ext <;> simp [zetaCylinderCoordinate, chartFunctionalDual,
    centeredSigma, heightCayley_neg]
  <;> ring

end InfoGeometry.Arithmetic.ZetaCenteredWallpaperKleinBridge

end noncomputable section

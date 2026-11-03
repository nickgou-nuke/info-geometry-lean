/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KreinCarrierInstances.Datum
import InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
import InfoGeometry.Arithmetic.SarnakLocalCertification

/-!
# The double-real Krein carrier and the centered Xi seam

This bridge identifies the carrier's fundamental symmetry with the
antiunitary critical-line reflection, and its affine glide with the existing
centered zeta wallpaper glide. It transfers the proved Xi zero-reflection
theorem through that explicit coordinate map; it does not assert Xi-periodicity
under the half-height glide.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge

open InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Canonical.HolographicSouriauClosure
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- The real double-Krein chart in centered zeta coordinates `(u,v)`, with
`u = -y` and `v = x`. -/
def kreinCenteredZetaCoord (p : KleinBottleCarrier) : CenteredZetaCoord :=
  (-WithLp.snd p, WithLp.fst p)

/-- The complex parameter represented by a point of the double-real chart. -/
def kreinCenteredParameter (p : KleinBottleCarrier) : ℂ :=
  (1 / 2 : ℂ) + (kreinCenteredZetaCoord p).1 +
    Complex.I * (kreinCenteredZetaCoord p).2

/-- The chart readout agrees with the repository's centered zeta coordinates. -/
theorem kreinCenteredParameter_coordinates (p : KleinBottleCarrier) :
    centeredZetaCoord (kreinCenteredParameter p) = kreinCenteredZetaCoord p := by
  apply Prod.ext
  · simp [kreinCenteredParameter, kreinCenteredZetaCoord, centeredZetaCoord]
  · simp [kreinCenteredParameter, kreinCenteredZetaCoord, centeredZetaCoord]

/-- The fundamental Krein symmetry is the antiunitary critical reflection in
the complex Xi parameter. -/
theorem fundamentalSymmetryKlein_intertwines_Xi_reflection
    (p : KleinBottleCarrier) :
    kreinCenteredParameter (fundamentalSymmetryKlein p) =
      antiunitaryCriticalReflection (kreinCenteredParameter p) := by
  apply Complex.ext
  · simp [kreinCenteredParameter, kreinCenteredZetaCoord,
      fundamentalSymmetryKlein_apply, antiunitaryCriticalReflection]
    ring
  · simp [kreinCenteredParameter, kreinCenteredZetaCoord,
      fundamentalSymmetryKlein_apply, antiunitaryCriticalReflection]

/-- The glide on the double-real carrier is exactly the wallpaper glide in
the centered zeta chart. -/
theorem MoebiusSymmetry_intertwines_centeredXi_glide
    (p : KleinBottleCarrier) :
    kreinCenteredZetaCoord (MoebiusSymmetry p) =
      zetaWallpaperGlide (kreinCenteredZetaCoord p) := by
  simp [kreinCenteredZetaCoord, MoebiusSymmetry, zetaWallpaperGlide,
    InfoGeometry.Canonical.HolographicSouriauClosure.glide_reflection]

/-- A point is fixed by the carrier's fundamental symmetry exactly when its
centered zeta coordinate lies on the critical seam. -/
theorem fundamentalSymmetry_fixed_iff_centeredCriticalSeam
    (p : KleinBottleCarrier) :
    fundamentalSymmetryKlein p = p ↔
      centeredCriticalSeam (kreinCenteredZetaCoord p) := by
  change fundamentalSymmetryKlein p = p ↔ -WithLp.snd p = 0
  constructor
  · intro h
    have hy : -WithLp.snd p = WithLp.snd p := by
      simpa [fundamentalSymmetryKlein] using congrArg WithLp.snd h
    linarith
  · intro h
    have hy : WithLp.snd p = 0 := by linarith
    apply (WithLp.ofLp_injective (p := (2 : ENNReal)))
    ext
    · simp [fundamentalSymmetryKlein]
    · simp [fundamentalSymmetryKlein, hy]

/-- The fixed space of the fundamental Krein symmetry is the critical line in
the represented complex parameter. -/
theorem fundamentalSymmetry_fixed_iff_OnCriticalLine
    (p : KleinBottleCarrier) :
    fundamentalSymmetryKlein p = p ↔
      OnCriticalLine (kreinCenteredParameter p) := by
  calc
    fundamentalSymmetryKlein p = p ↔
        centeredCriticalSeam (kreinCenteredZetaCoord p) :=
      fundamentalSymmetry_fixed_iff_centeredCriticalSeam p
    _ ↔ OnCriticalLine (kreinCenteredParameter p) := by
      rw [← kreinCenteredParameter_coordinates p]
      exact centeredZetaCoord_mem_seam_iff (kreinCenteredParameter p)

/-- The established Xi zero-reflection theorem transported to the concrete
double-real Krein carrier. -/
theorem entireRiemannXi_zero_reflection_of_fundamentalSymmetry
    {p : KleinBottleCarrier}
    (hzero : ActualRiemannXiEntireBridge.entireRiemannXi
      (kreinCenteredParameter p) = 0) :
    ActualRiemannXiEntireBridge.entireRiemannXi
      (kreinCenteredParameter (fundamentalSymmetryKlein p)) = 0 := by
  rw [fundamentalSymmetryKlein_intertwines_Xi_reflection]
  exact SarnakLocalCertification.entireRiemannXi_zero_reflection hzero

/-- Analytic Xi vanishing is equivalent at the two carrier points paired by
the fundamental symmetry. This is a carrier statement; no periodicity under
the separate wallpaper glide is assumed. -/
theorem entireRiemannXi_zero_iff_fundamentalSymmetry
    (p : KleinBottleCarrier) :
    ActualRiemannXiEntireBridge.entireRiemannXi
        (kreinCenteredParameter p) = 0 ↔
      ActualRiemannXiEntireBridge.entireRiemannXi
        (kreinCenteredParameter (fundamentalSymmetryKlein p)) = 0 := by
  rw [fundamentalSymmetryKlein_intertwines_Xi_reflection]
  exact SarnakLocalCertification.entireRiemannXi_zero_reflection_iff
    (kreinCenteredParameter p)

end InfoGeometry.Arithmetic.KreinCenteredXiGlideBridge

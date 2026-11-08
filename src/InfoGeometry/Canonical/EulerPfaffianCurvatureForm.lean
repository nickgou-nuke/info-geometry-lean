import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

import InfoGeometry.Volume.PfaffianPathBridge

/-!
# Finite oriented Pfaffian curvature readout

This is the finite algebraic layer for an Euler/Pfaffian density.  It uses
the existing signed `PfaffianMatchingExpansionPacket`; it does not reuse the
absolute-value Pfaffian from `Volume.Pfaffian` and does not claim a manifold
integration or Gauss--Bonnet theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.EulerPfaffianCurvatureForm

open InfoGeometry.Volume.PfaffianPathBridge

variable {R : Type*} [CommRing R]

/-- A finite oriented skew-curvature packet together with its signed
Pfaffian readout.  The orientation is represented by the signed matching
amplitude already owned by `PfaffianMatchingExpansionPacket`. -/
structure OrientedSkewCurvaturePacket where
  curvature : SkewPairingMatrixPacket
  pfaffianPacket : PfaffianMatchingExpansionPacket
  curvature_is_packet : pfaffianPacket.skewPairing = curvature

namespace OrientedSkewCurvaturePacket

variable (P : OrientedSkewCurvaturePacket)

/-- The signed finite Euler/Pfaffian density. -/
def eulerDensity : ℝ := P.pfaffianPacket.pfaffianAmplitude

/-- The underlying finite skew-curvature matrix. -/
def curvatureMatrix : Matrix P.curvature.Boundary P.curvature.Boundary ℝ :=
  P.curvature.W

theorem curvature_skew (i j : P.curvature.Boundary) :
    P.curvatureMatrix i j = -P.curvatureMatrix j i :=
  P.curvature.skew i j

theorem eulerDensity_eq_signed_matching_sum :
    P.eulerDensity =
      (letI : Fintype P.pfaffianPacket.PerfectPairing :=
        P.pfaffianPacket.pairingFinite
       Finset.univ.sum
        (fun p : P.pfaffianPacket.PerfectPairing =>
          P.pfaffianPacket.pairingSign p *
            P.pfaffianPacket.pairingProductWeight p)) := by
  exact pfaffian_eq_signed_pairing_sum P.pfaffianPacket

theorem determinantEvenVolume_eq_eulerDensity_sq :
    P.pfaffianPacket.determinantEvenVolume = P.eulerDensity ^ 2 := by
  exact determinant_even_volume_eq_pfaffian_sq P.pfaffianPacket

theorem determinantEvenVolume_nonneg :
    0 ≤ P.pfaffianPacket.determinantEvenVolume := by
  rw [P.determinantEvenVolume_eq_eulerDensity_sq]
  exact sq_nonneg P.eulerDensity

theorem determinantEvenVolume_eq_zero_iff_eulerDensity_eq_zero :
    P.pfaffianPacket.determinantEvenVolume = 0 ↔ P.eulerDensity = 0 := by
  rw [P.determinantEvenVolume_eq_eulerDensity_sq]
  exact sq_eq_zero_iff

end OrientedSkewCurvaturePacket

end InfoGeometry.Canonical.EulerPfaffianCurvatureForm

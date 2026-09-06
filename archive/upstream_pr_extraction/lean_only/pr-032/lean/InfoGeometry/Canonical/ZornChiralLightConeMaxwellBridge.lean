import InfoGeometry.Canonical.ZornAssociativeSpectralAdapter
import InfoGeometry.Canonical.ZornChiralLightConeCoordinates
import Mathlib.Tactic

/-!
# Light-cone/chiral Maxwell bridge

This owner composes the existing finite light-cone coordinate change with the
Zorn quadratic field readout.  It does not introduce PDE evolution or claim
that every field is a radiation field.
-/

namespace InfoGeometry.Canonical.ZornChiralLightConeMaxwellBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.ZornChiralLightConeCoordinates
open InfoGeometry.Canonical.ZornFieldSpectralReadout
open InfoGeometry.Canonical.ZornPotentialDifferentialReadout

theorem lightCone_lorenz_readout
    (du dv dminus dplus Au Av Aminus Aplus : ℝ) :
    lorenzScalar (du + dv) dminus dplus (dv - du)
        (Au + Av) Aminus Aplus (Av - Au) =
      2 * (du * Av + dv * Au) -
        (dminus * Aplus + dplus * Aminus) := by
  exact lorenzScalar_lightCone du dv dminus dplus Au Av Aminus Aplus

theorem lightCone_derivative_reconstruction
    (du dv : ℝ) :
    let d := lightConeDerivative du dv
    ((d.1 - d.2) / 2, (d.1 + d.2) / 2) = (du, dv) := by
  exact lightConeDerivative_reconstruct du dv

theorem null_field_zorn_square_zero
    {electric magnetic : ZornVec3 ℝ}
    (hnull : dot magnetic magnetic = dot electric electric) :
    mul
        (offDiagonal
          (fun i => -(electric i + magnetic i))
          (fun i => electric i - magnetic i))
        (offDiagonal
          (fun i => -(electric i + magnetic i))
          (fun i => electric i - magnetic i)) =
      zero := by
  rw [electricMagnetic_offDiagonal_square, hnull, sub_self]
  rfl

end InfoGeometry.Canonical.ZornChiralLightConeMaxwellBridge

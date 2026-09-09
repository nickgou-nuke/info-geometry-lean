import Mathlib.Tactic
import InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauSpecialization
import InfoGeometry.Arithmetic.PrimeGrandCanonicalMassieuBridge

/-!
# Native Souriau/Hestenes radial bridge

This file is a commuting-square layer, not a second thermodynamic owner.

The completed-Xi owner already supplies the universal-cover coordinates
`(rho, theta)` and the Hestenes Weyl mirror.  The Souriau owner already
supplies the finite moment pairing `beta * (E - mu * N)`, its partition
function, and the Legendre/Fenchel defect.  The prime owner already proves
that the finite partition is the corresponding Euler product.

The only new statements here identify the radial Cartan action with the
existing cylinder translation and record the exact finite prime readout.
No identification of the radial coordinate with inverse temperature, and no
completed-zeta moment-map theorem, is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.NativeSouriauHestenesRadialBridge

open InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates
open InfoGeometry.Canonical.CompletedXiHestenesHomogeneousCoordinates.LogCylinderCoordinate
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-! ## Radial Cartan/Weyl square -/

/-- The radial Cartan parameter acts by translation of `rho` by `2t`.

The factor `2` is forced by the homogeneous Cartan law
`tau ↦ exp (2t) * tau`; it is not identified here with a thermodynamic
inverse temperature.
-/
def radialCartanFlow (t : ℝ) (x : LogCylinderCoordinate) : LogCylinderCoordinate :=
  transverseTranslation (2 * t) x

theorem radialCartanFlow_apply (t : ℝ) (x : LogCylinderCoordinate) :
    radialCartanFlow t x =
      ⟨x.rho + 2 * t, x.theta⟩ := by
  rfl

@[simp]
theorem radialCartanFlow_zero (x : LogCylinderCoordinate) :
    radialCartanFlow 0 x = x := by
  cases x with
  | mk rho theta =>
      apply LogCylinderCoordinate.ext
      · norm_num [radialCartanFlow, transverseTranslation]
      · rfl

theorem radialCartanFlow_add (s t : ℝ) (x : LogCylinderCoordinate) :
    radialCartanFlow (s + t) x =
      radialCartanFlow s (radialCartanFlow t x) := by
  ext
  · simp [radialCartanFlow, transverseTranslation]; ring
  · simp [radialCartanFlow, transverseTranslation]

/-- The Weyl/radial mirror conjugates the Cartan flow to its inverse. -/
theorem radialMirror_radialCartanFlow_radialMirror
    (t : ℝ) (x : LogCylinderCoordinate) :
    radialMirror (radialCartanFlow t (radialMirror x)) =
      radialCartanFlow (-t) x := by
  ext
  · simp [radialMirror, radialCartanFlow, transverseTranslation]; ring
  · simp [radialMirror, radialCartanFlow, transverseTranslation]

theorem radialCartanFlow_rho (t : ℝ) (x : LogCylinderCoordinate) :
    (radialCartanFlow t x).rho = x.rho + 2 * t := by
  rfl

theorem radialMirror_rho (x : LogCylinderCoordinate) :
    (radialMirror x).rho = -x.rho := by
  rfl

/-! ## Native finite Souriau prime readout -/

theorem prime_souriau_weight_pairing
    (P : PrimeRegister)
    (energyWeight : ℕ → ℝ)
    (T : GeometricTemperature)
    (S : PrimeState P) :
    geometricTemperatureWeightPairing T
        (souriauWeightAt (primeSouriauMomentMap P energyWeight) S) =
      T.beta *
        (stateEnergy energyWeight S - T.mu * stateNumber S) := by
  rfl

/-
The following theorem is intentionally stated as the native owner equality,
not as a new partition definition.  It is the finite grand-canonical
commuting square: Souriau weights -> grand-canonical partition -> Euler
product.
-/
theorem prime_souriau_partition_euler_product
    (P : PrimeRegister)
    (energyWeight : ℕ → ℝ)
    (T : GeometricTemperature) :
    souriauPartition (primeSouriauMomentMap P energyWeight) T =
      (PrimeGrandCanonicalPacket.mk P energyWeight).finiteEulerProduct T.beta T.mu :=
  primeSouriauPartition_eq_finiteEulerProduct P energyWeight T

theorem prime_log_souriau_partition_euler_product
    (P : PrimeRegister)
    (T : GeometricTemperature) :
    souriauPartition (primeSouriauMomentMap P logPrimeEnergyWeight) T =
      (PrimeGrandCanonicalPacket.mk P logPrimeEnergyWeight).finiteEulerProduct T.beta T.mu :=
  prime_souriau_partition_euler_product P logPrimeEnergyWeight T

end InfoGeometry.Canonical.NativeSouriauHestenesRadialBridge

end noncomputable section

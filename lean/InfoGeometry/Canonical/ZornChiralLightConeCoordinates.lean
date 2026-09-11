import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral light-cone coordinate identities for the Zorn readout

This owner contains only finite linear coordinate algebra.  It does not model
derivatives as operators and does not assert Maxwell equations.
-/

namespace InfoGeometry.Canonical.ZornChiralLightConeCoordinates

noncomputable def lightConePotential (phi Az : ℝ) : ℝ × ℝ :=
  ((phi - Az) / 2, (phi + Az) / 2)

noncomputable def lightConePotentialEquiv : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun p := lightConePotential p.1 p.2
  invFun p := (p.1 + p.2, p.2 - p.1)
  left_inv := by
    intro p
    rcases p with ⟨phi, Az⟩
    simp [lightConePotential]
    constructor <;> ring
  right_inv := by
    intro p
    rcases p with ⟨Au, Av⟩
    simp [lightConePotential]
    constructor <;> ring

theorem lightConePotential_reconstruct (phi Az : ℝ) :
    let p := lightConePotential phi Az
    (p.1 + p.2, p.2 - p.1) = (phi, Az) := by
  dsimp [lightConePotential]
  ext <;> ring

noncomputable def lightConeDerivative (du dv : ℝ) : ℝ × ℝ :=
  (du + dv, dv - du)

noncomputable def lightConeDerivativeEquiv : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun p := lightConeDerivative p.1 p.2
  invFun p := ((p.1 - p.2) / 2, (p.1 + p.2) / 2)
  left_inv := by
    intro p
    rcases p with ⟨du, dv⟩
    simp [lightConeDerivative]
    constructor <;> ring
  right_inv := by
    intro p
    rcases p with ⟨dt, dz⟩
    simp [lightConeDerivative]
    constructor <;> ring

theorem lightConeDerivative_reconstruct (du dv : ℝ) :
    let d := lightConeDerivative du dv
    ((d.1 - d.2) / 2, (d.1 + d.2) / 2) = (du, dv) := by
  dsimp [lightConeDerivative]
  ext <;> ring

def lorenzScalar (dt dminus dplus dz phi Aminus Aplus Az : ℝ) : ℝ :=
  dt * phi - (dminus * Aplus + dplus * Aminus + dz * Az)

theorem lorenzScalar_lightCone (du dv dminus dplus Au Av Aminus Aplus : ℝ) :
    lorenzScalar (du + dv) dminus dplus (dv - du)
      (Au + Av) Aminus Aplus (Av - Au) =
      2 * (du * Av + dv * Au) - (dminus * Aplus + dplus * Aminus) := by
  dsimp [lorenzScalar]
  ring

end InfoGeometry.Canonical.ZornChiralLightConeCoordinates

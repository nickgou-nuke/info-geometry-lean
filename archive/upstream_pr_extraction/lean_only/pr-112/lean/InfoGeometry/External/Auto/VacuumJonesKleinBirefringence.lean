import InfoGeometry.External.Auto.OpticalAndreevSpinor
import InfoGeometry.External.Auto.ProjectiveKappaKleinMobius

/-!
# Vacuum Jones/Klein birefringence

Theorem-honest optical capstone:

* the Jones layer supplies circular spinors, half-wave chirality flips,
  determinant-one dichroic boosts, and determinant-one nonlinear axial gates;
* the Klein/projective layer supplies the glide half-shift, anticommuting
  Pauli atom, and square-root-of-minus-one monodromy.
-/

noncomputable section

namespace VacuumJonesKleinBirefringence

open Matrix Complex
open InfoGeometry.GrandUnification.OpticalAndreevSpinor
open ProjectiveKappaKleinMobius
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Jones-form vacuum dielectric tensor:
diagonal anisotropy plus antisymmetric optical-activity entry. -/
def vacuumJonesTensor (eps11 eps22 gamma : ℝ) : M2C :=
  !![(eps11 : ℂ), Complex.I * (gamma : ℂ);
     -Complex.I * (gamma : ℂ), (eps22 : ℂ)]

/-- Birefringence scalar: difference of the two principal entries. -/
def birefringenceDelta (eps11 eps22 : ℝ) : ℝ := eps11 - eps22

/-- The diagonal anisotropy of the Jones tensor is exactly `eps11 - eps22`. -/
theorem vacuumJonesTensor_birefringence (eps11 eps22 gamma : ℝ) :
    ((vacuumJonesTensor eps11 eps22 gamma 0 0) -
      (vacuumJonesTensor eps11 eps22 gamma 1 1)) =
      (birefringenceDelta eps11 eps22 : ℂ) := by
  simp [vacuumJonesTensor, birefringenceDelta]

/-- The optical-activity entry is the imaginary coupling `i gamma`. -/
theorem vacuumJonesTensor_optical_activity_upper (eps11 eps22 gamma : ℝ) :
    vacuumJonesTensor eps11 eps22 gamma 0 1 = Complex.I * (gamma : ℂ) := by
  simp [vacuumJonesTensor]

/-- The lower optical-activity entry is the conjugate-sign partner `-i gamma`. -/
theorem vacuumJonesTensor_optical_activity_lower (eps11 eps22 gamma : ℝ) :
    vacuumJonesTensor eps11 eps22 gamma 1 0 = -Complex.I * (gamma : ℂ) := by
  simp [vacuumJonesTensor]



end VacuumJonesKleinBirefringence

end noncomputable section

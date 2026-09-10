import InfoGeometry.External.Auto.OpticalAndreevSpinor
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

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



/-- Finite Jones/Klein aggregation theorem for the optical and projective matrix identities. -/
theorem vacuum_jones_klein_birefringence_synthesis
    (eps11 eps22 gamma alpha chi S3 : ℝ) :
    conjSpinor Rspinor = Lspinor ∧
    conjSpinor Lspinor = Rspinor ∧
    halfWavePlate * Rspinor = (-Complex.I) • Lspinor ∧
    halfWavePlate * Lspinor = (-Complex.I) • Rspinor ∧
    halfWavePlate.det = 1 ∧
    (jonesDichroicBoost alpha).det = 1 ∧
    Matrix.trace (axialSelfHamiltonian chi S3) = 0 ∧
    (nonlinearAxialGate chi S3).det = 1 ∧
    Mx * Ly = - (Ly * Mx) ∧
    (Mx * Ly) * (Mx * Ly) =
      (-1 : ℂ) • (1 : ProjectiveKappaKleinMobius.M2C) ∧
    (∀ k : KPoint, affineM (affineM k) = recipY k) ∧
    (∀ z : ℂ, halfShiftPhase (halfShiftPhase z) = z) ∧
    ((vacuumJonesTensor eps11 eps22 gamma 0 0) -
      (vacuumJonesTensor eps11 eps22 gamma 1 1)) =
      (birefringenceDelta eps11 eps22 : ℂ) ∧
    vacuumJonesTensor eps11 eps22 gamma 0 1 = Complex.I * (gamma : ℂ) ∧
    vacuumJonesTensor eps11 eps22 gamma 1 0 = -Complex.I * (gamma : ℂ) := by
  exact ⟨conj_Rspinor,
    conj_Lspinor,
    halfWavePlate_R,
    halfWavePlate_L,
    halfWavePlate_det,
    jonesDichroicBoost_det alpha,
    axialSelfHamiltonian_trace_zero chi S3,
    nonlinearAxialGate_det chi S3,
    Mx_Ly_anticomm,
    MxLy_sq_neg_one,
    affineM_sq,
    halfShiftPhase_sq,
    vacuumJonesTensor_birefringence eps11 eps22 gamma,
    vacuumJonesTensor_optical_activity_upper eps11 eps22 gamma,
    vacuumJonesTensor_optical_activity_lower eps11 eps22 gamma⟩

#check vacuumJonesTensor_birefringence
#check vacuumJonesTensor_optical_activity_upper
#check vacuum_jones_klein_birefringence_synthesis

end VacuumJonesKleinBirefringence

end noncomputable section

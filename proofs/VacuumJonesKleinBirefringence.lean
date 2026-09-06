import proofs.OpticalAndreevSpinor
import proofs.ProjectiveKappaKleinMobius
import InfoGeometry.Canonical.ChiralCausalCone
import proofs.ChiralIsospinEOMSU2

/-!
# Vacuum Jones/Klein birefringence

Theorem-honest optical capstone:

* the Jones layer supplies circular spinors, half-wave chirality flips,
  determinant-one dichroic boosts, and determinant-one nonlinear axial gates;
* the Klein/projective layer supplies the glide half-shift, anticommuting
  Pauli atom, and square-root-of-minus-one monodromy;
* the wallpaper/GNS layer supplies the Raman-style selection rule:
  only the trivial `S₃` sector is active.
-/

noncomputable section

namespace VacuumJonesKleinBirefringence

open Matrix Complex
open InfoGeometry.GrandUnification.OpticalAndreevSpinor
open ProjectiveKappaKleinMobius

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Local copy of the three `S₃` optical sectors used by the Raman selection
rule.  This mirrors the wallpaper capstone without depending on its namespace
export behavior. -/
inductive OpticalS3Sector where
  | trivial
  | sign
  | standard
  deriving DecidableEq, Repr

/-- Optical/Raman activity: only the totally symmetric sector survives. -/
def OpticalRamanActive (ρ : OpticalS3Sector) : Prop :=
  ρ = OpticalS3Sector.trivial

/-- The local optical selection rule is exactly trivial-sector activity. -/
theorem optical_raman_active_iff_trivial (ρ : OpticalS3Sector) :
    OpticalRamanActive ρ ↔ ρ = OpticalS3Sector.trivial := by
  cases ρ <;> simp [OpticalRamanActive]

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



/-- Finite optical/Klein selection theorem. It proves the algebraic Jones,
glide, and Raman-selection anchors. -/
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
    (∀ ρ : OpticalS3Sector, OpticalRamanActive ρ ↔ ρ = OpticalS3Sector.trivial) ∧
    ((vacuumJonesTensor eps11 eps22 gamma 0 0) -
      (vacuumJonesTensor eps11 eps22 gamma 1 1)) =
      (birefringenceDelta eps11 eps22 : ℂ) ∧
    vacuumJonesTensor eps11 eps22 gamma 0 1 = Complex.I * (gamma : ℂ) ∧
    vacuumJonesTensor eps11 eps22 gamma 1 0 = -Complex.I * (gamma : ℂ) ∧
    ChiralCausalCone.PPlus + ChiralCausalCone.PMinus =
      (1 : ChiralCausalCone.M2C) := by
  constructor
  · exact conj_Rspinor
  constructor
  · exact conj_Lspinor
  constructor
  · simpa using halfWavePlate_R
  constructor
  · simpa using halfWavePlate_L
  constructor
  · simpa using halfWavePlate_det
  constructor
  · exact jonesDichroicBoost_det alpha
  constructor
  · exact axialSelfHamiltonian_trace_zero chi S3
  constructor
  · exact nonlinearAxialGate_det chi S3
  constructor
  · exact Mx_Ly_anticomm
  constructor
  · exact MxLy_sq_neg_one
  constructor
  · exact affineM_sq
  constructor
  · simpa using halfShiftPhase_sq
  constructor
  · exact optical_raman_active_iff_trivial
  constructor
  · exact vacuumJonesTensor_birefringence eps11 eps22 gamma
  constructor
  · exact vacuumJonesTensor_optical_activity_upper eps11 eps22 gamma
  constructor
  · exact vacuumJonesTensor_optical_activity_lower eps11 eps22 gamma
  · exact ChiralCausalCone.PPlus_add_PMinus

#check vacuumJonesTensor_birefringence
#check vacuumJonesTensor_optical_activity_upper
#check vacuum_jones_klein_birefringence_synthesis

end VacuumJonesKleinBirefringence

end noncomputable section

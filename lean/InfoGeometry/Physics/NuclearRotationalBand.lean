import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearAngularMomentum

noncomputable section

namespace InfoGeometry.Physics.NuclearRotationalBand

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦] [CharZero 𝒦]

def moment_of_inertia (hbar : 𝒦) (mass_radius_sq : 𝒦) (deformation_factor : 𝒦) : 𝒦 :=
  mass_radius_sq * (1 + deformation_factor * deformation_factor)

theorem moment_of_inertia_homogeneous (hbar : 𝒦) (mass_radius_sq : 𝒦) (deformation_factor : 𝒦) (lam : 𝒦) :
    moment_of_inertia hbar (lam * mass_radius_sq) deformation_factor = lam * moment_of_inertia hbar mass_radius_sq deformation_factor := by
  calc
    moment_of_inertia hbar (lam * mass_radius_sq) deformation_factor =
        (lam * mass_radius_sq) * (1 + deformation_factor * deformation_factor) := by rfl
    _ = lam * (mass_radius_sq * (1 + deformation_factor * deformation_factor)) := by ring
    _ = lam * moment_of_inertia hbar mass_radius_sq deformation_factor := by rfl

def rotational_energy (hbar : 𝒦) (𝓘 : 𝒦) (I : 𝒦) : 𝒦 :=
  (hbar * hbar : 𝒦) * I * (I + 1 : 𝒦) / (2 * 𝓘 : 𝒦)

theorem rotational_energy_spacing (hbar : 𝒦) (𝓘 : 𝒦) (I : 𝒦) :
    rotational_energy hbar 𝓘 (I + 1) - rotational_energy hbar 𝓘 I =
      (hbar * hbar : 𝒦) * (I + 1 : 𝒦) / 𝓘 := by
  have h₁ : rotational_energy hbar 𝓘 (I + 1) = (hbar * hbar : 𝒦) * (I + 1 : 𝒦) * ((I + 1 : 𝒦) + (1 : 𝒦)) / (2 * 𝓘 : 𝒦) := by
    rfl
  have h₂ : rotational_energy hbar 𝓘 I = (hbar * hbar : 𝒦) * I * (I + 1 : 𝒦) / (2 * 𝓘 : 𝒦) := by
    rfl
  rw [h₁, h₂]
  field_simp
  <;> ring
  <;> field_simp
  <;> ring

end InfoGeometry.Physics.NuclearRotationalBand

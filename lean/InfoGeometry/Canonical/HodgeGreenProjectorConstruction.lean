import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinSpectralFittingBridge
import InfoGeometry.Canonical.HodgeHelmholtzKreinDecomposition

namespace InfoGeometry.Canonical.HodgeGreenProjectorConstruction

open Drazin HodgeHelmholtzKreinDecomposition

section Ring

variable {Algebra : Type*} [Ring Algebra]

theorem exact_coexact_product_zero (differential codifferential green : Algebra)
    (codifferential_sq : codifferential * codifferential = 0)
    (commutes : green * codifferential = codifferential * green) :
    (differential * codifferential * green) * (codifferential * differential * green) = 0 := by
  calc
    (differential * codifferential * green) * (codifferential * differential * green) =
        differential * (codifferential * (green * codifferential)) * differential * green := by
      noncomm_ring
    _ = differential * (codifferential * (codifferential * green)) * differential * green := by
      rw [commutes]
    _ = differential * (codifferential * codifferential) * green * differential * green := by
      noncomm_ring
    _ = 0 := by rw [codifferential_sq]; simp

theorem exact_projector_idempotent (differential codifferential green : Algebra)
    (codifferential_sq : codifferential * codifferential = 0)
    (commutes : green * codifferential = codifferential * green)
    (reflexive : green * (differential * codifferential + codifferential * differential) * green =
      green) :
    (differential * codifferential * green) * (differential * codifferential * green) =
      differential * codifferential * green := by
  have resolution :
      (differential * codifferential * green) *
        (differential * codifferential * green + codifferential * differential * green) =
      differential * codifferential * green := by
    calc
      _ = (differential * codifferential) *
          (green * (differential * codifferential + codifferential * differential) * green) := by
        noncomm_ring
      _ = _ := by rw [reflexive]
  rw [mul_add, exact_coexact_product_zero differential codifferential green
    codifferential_sq commutes, add_zero] at resolution
  exact resolution

end Ring

section Module

variable {Scalar Space : Type*} [Ring Scalar] [AddCommGroup Space] [Module Scalar Space]
variable (system : HodgePacket (R := Scalar) (V := Space))
variable (green : Module.End Scalar Space) {index : ℕ}
variable (inverse : IsDrazinInverse system.Δ green index)
variable (commutes_d : green * system.d = system.d * green)
variable (commutes_cod : green * system.δ = system.δ * green)

def decompositionFromGreen :
    HodgePacket.DecompositionPacket (R := Scalar) (V := Space) := by
  let exactProj := system.d * system.δ * green
  let coexactProj := system.δ * system.d * green
  have differential_sq : system.d * system.d = 0 := system.d_sq
  have codifferential_sq : system.δ * system.δ = 0 := system.δ_sq
  have reflexive : green * (system.d * system.δ + system.δ * system.d) * green = green := by
    simpa only [system.Δ_def] using inverse.idempotent
  have exact_sq : exactProj * exactProj = exactProj :=
    exact_projector_idempotent system.d system.δ green codifferential_sq commutes_cod reflexive
  have coexact_sq : coexactProj * coexactProj = coexactProj :=
    exact_projector_idempotent system.δ system.d green differential_sq commutes_d
      (by simpa only [add_comm] using reflexive)
  have cross : exactProj * coexactProj = 0 :=
    exact_coexact_product_zero system.d system.δ green codifferential_sq commutes_cod
  have reverse_cross : coexactProj * exactProj = 0 :=
    exact_coexact_product_zero system.δ system.d green differential_sq commutes_d
  refine {
    Pex := exactProj
    Pcoex := coexactProj
    Pharm := 1 - (exactProj + coexactProj)
    Pex_idem := exact_sq
    Pcoex_idem := coexact_sq
    Pharm_idem := ?_
    Pex_Pcoex_zero := cross
    Pcoex_Pex_zero := reverse_cross
    Pex_Pharm_zero := ?_
    Pharm_Pex_zero := ?_
    Pcoex_Pharm_zero := ?_
    Pharm_Pcoex_zero := ?_
    partition_unity := ?_ }
  · change (1 - (exactProj + coexactProj)) * (1 - (exactProj + coexactProj)) = _
    noncomm_ring [exact_sq, coexact_sq, cross, reverse_cross]
  · change exactProj * (1 - (exactProj + coexactProj)) = 0
    rw [mul_sub, mul_one, mul_add, exact_sq, cross, add_zero, sub_self]
  · change (1 - (exactProj + coexactProj)) * exactProj = 0
    rw [sub_mul, one_mul, add_mul, exact_sq, reverse_cross, add_zero, sub_self]
  · change coexactProj * (1 - (exactProj + coexactProj)) = 0
    rw [mul_sub, mul_one, mul_add, reverse_cross, coexact_sq, zero_add, sub_self]
  · change (1 - (exactProj + coexactProj)) * coexactProj = 0
    rw [sub_mul, one_mul, add_mul, cross, coexact_sq, zero_add, sub_self]
  · noncomm_ring

theorem harmonic_projector_eq_drazin :
    (decompositionFromGreen system green inverse commutes_d commutes_cod).Pharm =
      IsDrazinInverse.complementaryProjection system.Δ green := by
  change 1 - (system.d * system.δ * green + system.δ * system.d * green) = _
  simp only [IsDrazinInverse.complementaryProjection, IsDrazinInverse.projection,
    system.Δ_def, add_mul]
  rfl

theorem exact_component_mem_range (state : Space) :
    (decompositionFromGreen system green inverse commutes_d commutes_cod).Pex state ∈
      LinearMap.range system.d :=
  ⟨system.δ (green state), rfl⟩

theorem coexact_component_mem_range (state : Space) :
    (decompositionFromGreen system green inverse commutes_d commutes_cod).Pcoex state ∈
      LinearMap.range system.δ :=
  ⟨system.d (green state), rfl⟩

theorem harmonic_component_mem_power_kernel (state : Space) :
    (decompositionFromGreen system green inverse commutes_d commutes_cod).Pharm state ∈
      LinearMap.ker (system.Δ ^ index) := by
  rw [harmonic_projector_eq_drazin]
  exact LinearMap.congr_fun
    (IsDrazinInverse.power_mul_complementaryProjection_eq_zero inverse) state

theorem harmonic_projector_range_eq_power_kernel :
    LinearMap.range
      (decompositionFromGreen system green inverse commutes_d commutes_cod).Pharm =
      LinearMap.ker (system.Δ ^ index) := by
  ext state
  constructor
  · rintro ⟨source, rfl⟩
    exact harmonic_component_mem_power_kernel system green inverse commutes_d commutes_cod source
  · intro in_kernel
    have green_zero : green state = 0 :=
      DrazinSpectralFittingBridge.drazin_annihilates_nilpotent inverse state in_kernel
    refine ⟨state, ?_⟩
    rw [harmonic_projector_eq_drazin]
    change (1 - system.Δ * green) state = state
    simp [Module.End.mul_apply, green_zero]

theorem harmonic_projector_range_eq_kernel
    (group_inverse : IsDrazinInverse system.Δ green 1) :
    LinearMap.range
      (decompositionFromGreen system green group_inverse commutes_d commutes_cod).Pharm =
      LinearMap.ker system.Δ := by
  simpa only [pow_one] using
    harmonic_projector_range_eq_power_kernel system green group_inverse commutes_d commutes_cod

end Module

end InfoGeometry.Canonical.HodgeGreenProjectorConstruction

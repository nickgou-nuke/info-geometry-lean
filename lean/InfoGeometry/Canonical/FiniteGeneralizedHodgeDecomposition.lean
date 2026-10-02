import InfoGeometry.Canonical.DrazinCommutant
import InfoGeometry.Canonical.DrazinExistenceBridge
import InfoGeometry.Canonical.HodgeGreenProjectorConstruction

namespace InfoGeometry.Canonical.FiniteGeneralizedHodgeDecomposition

open Drazin HodgeHelmholtzKreinDecomposition HodgeGreenProjectorConstruction

variable {Scalar Space : Type*} [DivisionRing Scalar] [AddCommGroup Space]
variable [Module Scalar Space] [FiniteDimensional Scalar Space]
variable (system : HodgePacket (R := Scalar) (V := Space))

theorem exists_commuting_green :
    ∃ (index : ℕ) (green : Module.End Scalar Space),
      IsDrazinInverse system.Δ green index ∧
        green * system.d = system.d * green ∧ green * system.δ = system.δ * green := by
  obtain ⟨index, green, inverse⟩ :=
    DrazinExistenceBridge.exists_canonicalDrazinInverse_global system.Δ
  refine ⟨index, green, inverse, ?_, ?_⟩
  · apply DrazinCommutant.inverse_commutes_of_commutes inverse system.d
    exact (sub_eq_zero.mp system.d_commutes_Δ).symm
  · apply DrazinCommutant.inverse_commutes_of_commutes inverse system.δ
    exact (sub_eq_zero.mp system.δ_commutes_Δ).symm

theorem exists_generalized_hodge_decomposition :
    ∃ (index : ℕ) (packet : HodgePacket.DecompositionPacket (R := Scalar) (V := Space)),
      LinearMap.range packet.Pex ≤ LinearMap.range system.d ∧
        LinearMap.range packet.Pcoex ≤ LinearMap.range system.δ ∧
        LinearMap.range packet.Pharm = LinearMap.ker (system.Δ ^ index) := by
  obtain ⟨index, green, inverse, commutes_d, commutes_cod⟩ := exists_commuting_green system
  refine ⟨index, decompositionFromGreen system green inverse commutes_d commutes_cod, ?_, ?_, ?_⟩
  · rintro state ⟨source, rfl⟩
    exact exact_component_mem_range system green inverse commutes_d commutes_cod source
  · rintro state ⟨source, rfl⟩
    exact coexact_component_mem_range system green inverse commutes_d commutes_cod source
  · exact harmonic_projector_range_eq_power_kernel system green inverse commutes_d commutes_cod

end InfoGeometry.Canonical.FiniteGeneralizedHodgeDecomposition

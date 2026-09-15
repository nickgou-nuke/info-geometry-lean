import InfoGeometry.Canonical.FiniteGeneralizedHodgeDecomposition
import InfoGeometry.HodgeCohomology.KreinGreenEnergy

namespace InfoGeometry.HodgeCohomology.KreinFiniteGreenDecomposition

open InfoGeometry.Canonical
open HodgeHelmholtzKreinDecomposition HodgeGreenProjectorConstruction

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space] [FiniteDimensional ℝ Space]
variable (pairing : LinearMap.BilinForm ℝ Space)
variable (system : HodgePacket (R := ℝ) (V := Space))

theorem exists_adjoint_generalized_decomposition
    (symmetric : pairing.IsSymm)
    (adjunction : LinearMap.IsAdjointPair pairing pairing system.d system.δ) :
    ∃ (index : ℕ) (packet : HodgePacket.DecompositionPacket (R := ℝ) (V := Space)),
      LinearMap.range packet.Pex ≤ LinearMap.range system.d ∧
      LinearMap.range packet.Pcoex ≤ LinearMap.range system.δ ∧
      LinearMap.range packet.Pharm = LinearMap.ker (system.Δ ^ index) ∧
      LinearMap.IsAdjointPair pairing pairing packet.Pex packet.Pex ∧
      LinearMap.IsAdjointPair pairing pairing packet.Pcoex packet.Pcoex ∧
      LinearMap.IsAdjointPair pairing pairing packet.Pharm packet.Pharm := by
  obtain ⟨index, green, inverse, commutes_d, commutes_cod⟩ :=
    FiniteGeneralizedHodgeDecomposition.exists_commuting_green system
  refine ⟨index, decompositionFromGreen system green inverse commutes_d commutes_cod, ?_, ?_, ?_, ?_⟩
  · rintro state ⟨source, rfl⟩
    exact exact_component_mem_range system green inverse commutes_d commutes_cod source
  · rintro state ⟨source, rfl⟩
    exact coexact_component_mem_range system green inverse commutes_d commutes_cod source
  · exact harmonic_projector_range_eq_power_kernel system green inverse commutes_d commutes_cod
  · exact KreinGreenEnergy.constructed_projectors_adjoint pairing system green inverse
      commutes_d commutes_cod symmetric adjunction

end InfoGeometry.HodgeCohomology.KreinFiniteGreenDecomposition

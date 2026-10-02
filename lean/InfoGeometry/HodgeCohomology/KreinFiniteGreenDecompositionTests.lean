import InfoGeometry.HodgeCohomology.KreinFiniteGreenDecomposition
import InfoGeometry.HodgeCohomology.KreinNilpotentGreenTests

namespace InfoGeometry.HodgeCohomology.KreinFiniteGreenDecomposition.Tests

open InfoGeometry.Canonical
open HodgeHelmholtzKreinDecomposition HodgeGreenProjectorConstruction.Tests

example : ∃ (index : ℕ) (packet : HodgePacket.DecompositionPacket (R := ℝ) (V := Triple)),
    LinearMap.range packet.Pharm = LinearMap.ker (tripleSystem.Δ ^ index) ∧
    ∀ state, KreinGreenEnergy.Tests.signedPairing state state =
      KreinGreenEnergy.Tests.signedPairing (packet.Pex state) (packet.Pex state) +
      KreinGreenEnergy.Tests.signedPairing (packet.Pcoex state) (packet.Pcoex state) +
      KreinGreenEnergy.Tests.signedPairing (packet.Pharm state) (packet.Pharm state) := by
  obtain ⟨index, packet, _, _, sector, exact_adjoint, coexact_adjoint, harmonic_adjoint⟩ :=
    exists_adjoint_generalized_decomposition KreinGreenEnergy.Tests.signedPairing tripleSystem
      KreinGreenEnergy.Tests.signedPairing_symmetric KreinGreenEnergy.Tests.differential_adjoint
  exact ⟨index, packet, sector, KreinGreenEnergy.signed_projector_energy
    KreinGreenEnergy.Tests.signedPairing packet exact_adjoint coexact_adjoint harmonic_adjoint⟩

example : ∃ (index : ℕ) (packet : HodgePacket.DecompositionPacket (R := ℝ) (V := Triple)),
    LinearMap.range packet.Pharm = LinearMap.ker (KreinNilpotentGreen.Tests.system.Δ ^ index) ∧
    LinearMap.IsAdjointPair KreinNilpotentGreen.Tests.pairing KreinNilpotentGreen.Tests.pairing
      packet.Pharm packet.Pharm := by
  obtain ⟨index, packet, _, _, sector, _, _, harmonic_adjoint⟩ :=
    exists_adjoint_generalized_decomposition KreinNilpotentGreen.Tests.pairing
      KreinNilpotentGreen.Tests.system KreinNilpotentGreen.Tests.pairing_symmetric
      KreinNilpotentGreen.Tests.adjunction
  exact ⟨index, packet, sector, harmonic_adjoint⟩

#print axioms exists_adjoint_generalized_decomposition

end InfoGeometry.HodgeCohomology.KreinFiniteGreenDecomposition.Tests

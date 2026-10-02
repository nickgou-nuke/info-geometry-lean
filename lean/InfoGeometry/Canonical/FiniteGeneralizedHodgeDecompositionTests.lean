import InfoGeometry.Canonical.FiniteGeneralizedHodgeDecomposition
import InfoGeometry.Canonical.HodgeGreenProjectorConstructionTests

namespace InfoGeometry.Canonical.FiniteGeneralizedHodgeDecomposition.Tests

open HodgeHelmholtzKreinDecomposition HodgeGreenProjectorConstruction.Tests
open InfoGeometry.HodgeCohomology.KreinHodgeObstruction

example : ∃ (index : ℕ) (packet : HodgePacket.DecompositionPacket (R := ℝ) (V := Triple)),
    LinearMap.range packet.Pex ≤ LinearMap.range tripleSystem.d ∧
      LinearMap.range packet.Pcoex ≤ LinearMap.range tripleSystem.δ ∧
      LinearMap.range packet.Pharm = LinearMap.ker (tripleSystem.Δ ^ index) :=
  exists_generalized_hodge_decomposition tripleSystem

example : ∃ (index : ℕ) (packet : HodgePacket.DecompositionPacket (R := ℝ) (V := Plane)),
    LinearMap.range packet.Pex ≤ LinearMap.range nullSystem.d ∧
      LinearMap.range packet.Pcoex ≤ LinearMap.range nullSystem.δ ∧
      LinearMap.range packet.Pharm = LinearMap.ker (nullSystem.Δ ^ index) :=
  exists_generalized_hodge_decomposition nullSystem

example {Algebra : Type*} [Ring Algebra] (operator : Algebra) :
    (1 : Algebra) * operator = operator * 1 := by
  apply DrazinCommutant.inverse_commutes_of_commutes
    (operator := (1 : Algebra)) (index := 0)
  · exact ⟨rfl, by simp, by simp⟩
  · simp

#print axioms DrazinCommutant.inverse_commutes_of_commutes
#print axioms exists_commuting_green
#print axioms exists_generalized_hodge_decomposition

end InfoGeometry.Canonical.FiniteGeneralizedHodgeDecomposition.Tests

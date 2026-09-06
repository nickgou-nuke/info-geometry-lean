import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

namespace InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellTwoBoundary

open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

/- The raw left-factor residual coordinates are not faithful on cell 2.
   These are closed native computations, not an external cardinality claim. -/
set_option maxRecDepth 100000 in
theorem residualWord_cell_two_collision :
    residualWord 2 170 = residualWord 2 185 ∧
      (170 : Fin 189) ∈ orbitCells 2 ∧
      (185 : Fin 189) ∈ orbitCells 2 ∧
      (170 : Fin 189) ≠ 185 := by
  decide

set_option maxRecDepth 100000 in
theorem residualWord_injective_on_cell_two_is_false :
    ¬ (∀ i j : Fin 189,
      i ∈ orbitCells 2 → j ∈ orbitCells 2 →
      residualWord 2 i = residualWord 2 j → i = j) := by
  intro h
  exact residualWord_cell_two_collision.2.2.2
    (h 170 185 residualWord_cell_two_collision.2.1
      residualWord_cell_two_collision.2.2.1
      residualWord_cell_two_collision.1)

end InfoGeometry.Algebra.Zorn.G2ResidualCoordinateCellTwoBoundary

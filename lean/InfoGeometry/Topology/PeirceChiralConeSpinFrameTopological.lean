import InfoGeometry.Canonical.CubicJordanOsTopologicalReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Closed coordinate channels for the native Peirce decomposition

The algebraic Peirce owner exposes coordinate projections of the native
`AlbertMatrix` carrier.  This file adds only their topological level sets.
It does not introduce a Jordan product, an eigenvalue theorem, or an
embedding of a Clifford algebra into an Albert component.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

def peirce23CoordinateLevelSet (z : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct) : Set AlbertMatrix :=
  {X | X.z₁ = z}

def peirce31CoordinateLevelSet (z : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct) : Set AlbertMatrix :=
  {X | X.z₂ = z}

def peirce12CoordinateLevelSet (z : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct) : Set AlbertMatrix :=
  {X | X.z₃ = z}

theorem isClosed_peirce23CoordinateLevelSet (z : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct) :
    IsClosed (peirce23CoordinateLevelSet z) := by
  exact isClosed_singleton.preimage continuous_albertMatrix_z₁

theorem isClosed_peirce31CoordinateLevelSet (z : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct) :
    IsClosed (peirce31CoordinateLevelSet z) := by
  exact isClosed_singleton.preimage continuous_albertMatrix_z₂

theorem isClosed_peirce12CoordinateLevelSet (z : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct) :
    IsClosed (peirce12CoordinateLevelSet z) := by
  exact isClosed_singleton.preimage continuous_albertMatrix_z₃

theorem peirce_chiral_coordinate_level_sets_closed
    (z₂₃ z₃₁ z₁₂ : InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication.SplitOct) :
    IsClosed (peirce23CoordinateLevelSet z₂₃) ∧
    IsClosed (peirce31CoordinateLevelSet z₃₁) ∧
    IsClosed (peirce12CoordinateLevelSet z₁₂) := by
  exact ⟨isClosed_peirce23CoordinateLevelSet z₂₃,
    isClosed_peirce31CoordinateLevelSet z₃₁,
    isClosed_peirce12CoordinateLevelSet z₁₂⟩

end InfoGeometry.Topology

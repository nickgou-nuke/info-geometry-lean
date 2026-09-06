import InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

/-!
# Finite support of the exterior spinor

The graded basis of the exterior algebra is reindexed by the finite type of
finite subsets of `Fin 5`.  This is the canonical finite-support step; no
coordinate carrier is introduced before the dimension theorem.
-/

namespace InfoGeometry.Clifford.SplitClifford55ExteriorFiniteSupport

open InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

theorem exteriorAlgebra_finiteDimensional :
    FiniteDimensional ℝ (ExteriorAlgebra ℝ V) := by
  exact Module.Basis.finiteDimensional_of_finite exteriorAlgebraBasisFinset

end InfoGeometry.Clifford.SplitClifford55ExteriorFiniteSupport

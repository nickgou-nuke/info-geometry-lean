import InfoGeometry.OperatorAlgebra.SpinorMetric
import InfoGeometry.OperatorAlgebra.StateTangentVector
import InfoGeometry.OperatorAlgebra.SpinorMetricDependency
import InfoGeometry.QuantumGeometry.SLDTraceMetric

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SpinorMetricTests

open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.CStarMatrixTowerIsometry
open InfoGeometry.QuantumGeometry.SLD
open SpinorMetric
open scoped ComplexOrder

example : NormedAddCommGroup (StateTangentVector ℂ) := inferInstance
example : NormedSpace ℝ (StateTangentVector ℂ) := inferInstance
example : CompleteSpace (StateTangentVector ℂ) := inferInstance

example (tangent : StateTangentVector ℂ) : tangent.val = 0 := by
  apply ContinuousLinearMap.ext
  intro scalar
  exact tangent_vanishes_on_scalar ℂ tangent scalar

example : Isometry (cstarConcreteStep 0) := cstarConcreteStep_isometry 0

example (matrix : CStarMatrixStage 1) : ‖cstarConcreteMap (by decide : 1 ≤ 4) matrix‖ = ‖matrix‖ :=
  cstarConcreteMap_norm (by decide) matrix

example : IsSLD (Matrix.diagonal (fun index : Fin 2 => (![1 / 3, 2 / 3] : Fin 2 → ℝ) index))
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 2; 2, 0] := by
  apply (isSLD_diagonal_iff (![1 / 3, 2 / 3] : Fin 2 → ℝ)
    (by intro index; fin_cases index <;> norm_num) _ _).mpr
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [diagonalSLD]

example : ¬ ∃ score : Matrix (Fin 1) (Fin 1) ℂ, IsSLD 0 1 score := by
  simp [IsSLD, jordanProd]

example (variation : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃! score, IsSLD 1 variation score :=
  existsUnique_sld_of_posDef 1 variation Matrix.PosDef.one

example (variation : Matrix (Fin 2) (Fin 2) ℂ) (self_adjoint : star variation = variation) :
    0 ≤ buresTangentMetric 1 Matrix.PosDef.one variation variation :=
  buresTangentMetric_nonneg 1 Matrix.PosDef.one variation self_adjoint

#print axioms cstarConcreteMap_isometry
#print axioms cstarConcreteStep_isometry
#print axioms cstarMatrixTraceState_strictly_positive
#print axioms existsUnique_sld_of_posDef
#print axioms existsUnique_selfAdjoint_sld
#print axioms lyapunovLinearMap_bijective
#print axioms sld_solves
#print axioms sld_selfAdjoint
#print axioms buresTangentMetric_symm
#print axioms buresTangentMetric_nonneg
#print axioms helstromMetric_nonneg
#print axioms finite_trace_bures_positive
#print axioms isClosed_stateTangentSubmodule
#print axioms tangent_vanishes_on_scalar
#print axioms SpinorMetricDependency.independent_branches

end InfoGeometry.OperatorAlgebra.SpinorMetricTests

import InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
import Mathlib.Analysis.CStarAlgebra.Hom

noncomputable section

namespace InfoGeometry.Canonical.CStarMatrixTowerIsometry

open CantorBernoulliCStarMatrixTraceState
open scoped ComplexOrder

theorem cstarConcreteMap_injective {earlier later : ℕ} (order : earlier ≤ later) :
    Function.Injective (cstarConcreteMap order) := by
  intro first second equal
  apply sub_eq_zero.mp
  apply (cstarMatrixTraceState_faithful earlier (first - second)).mp
  rw [← cstarMatrixTraceState_transition_general order]
  have difference_zero : cstarConcreteMap order (first - second) = 0 := by
    rw [map_sub, equal, sub_self]
  rw [map_mul, map_star, difference_zero, star_zero, zero_mul, map_zero]

theorem cstarConcreteStep_injective (stage : ℕ) :
    Function.Injective (cstarConcreteStep stage) := by
  intro first second equal
  apply sub_eq_zero.mp
  apply (cstarMatrixTraceState_faithful stage (first - second)).mp
  rw [← cstarMatrixTraceState_transition stage]
  have difference_zero : cstarConcreteStep stage (first - second) = 0 := by
    rw [map_sub, equal, sub_self]
  rw [map_mul, map_star, difference_zero, star_zero, zero_mul, map_zero]

theorem cstarConcreteMap_isometry {earlier later : ℕ} (order : earlier ≤ later) :
    Isometry (cstarConcreteMap order) :=
  NonUnitalStarAlgHom.isometry _ (cstarConcreteMap_injective order)

theorem cstarConcreteStep_isometry (stage : ℕ) :
    Isometry (cstarConcreteStep stage) :=
  NonUnitalStarAlgHom.isometry _ (cstarConcreteStep_injective stage)

theorem cstarConcreteMap_norm {earlier later : ℕ} (order : earlier ≤ later)
    (matrix : CStarMatrixStage earlier) :
    ‖cstarConcreteMap order matrix‖ = ‖matrix‖ :=
  NonUnitalStarAlgHom.norm_map _ (cstarConcreteMap_injective order) matrix

theorem cstarConcreteStep_norm (stage : ℕ) (matrix : CStarMatrixStage stage) :
    ‖cstarConcreteStep stage matrix‖ = ‖matrix‖ :=
  NonUnitalStarAlgHom.norm_map _ (cstarConcreteStep_injective stage) matrix

theorem cstarMatrixInductiveSystem_isometry {earlier later : ℕ}
    (order : earlier ≤ later) :
    Isometry (cstarMatrixInductiveSystem.map order) :=
  cstarConcreteMap_isometry order

theorem cstarMatrixTraceState_strictly_positive (stage : ℕ)
    (matrix : CStarMatrixStage stage) (nonzero : matrix ≠ 0) :
    0 < ((cstarMatrixTraceState stage).functional (star matrix * matrix)).re := by
  have positive := CStarStateColimit.PositiveState.gns_state_pos
    (cstarMatrixTraceState stage).functional matrix
  apply lt_of_le_of_ne positive
  intro real_zero
  apply nonzero
  apply (cstarMatrixTraceState_faithful stage matrix).mp
  apply Complex.ext
  · exact real_zero.symm
  · exact CStarStateColimit.PositiveState.gns_state_self_star_real
      (cstarMatrixTraceState stage).functional matrix

end InfoGeometry.Canonical.CStarMatrixTowerIsometry

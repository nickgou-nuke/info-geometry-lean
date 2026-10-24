/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GrowingOnsiteMatrixNorm
import InfoGeometry.Canonical.GrowingOnsiteCommutatorTransport
import InfoGeometry.Canonical.FilteredTracialGNSCommutatorTransport
import InfoGeometry.Canonical.FilteredGNSHilbertColimit
import InfoGeometry.Canonical.FilteredCompatibleOperatorSelfAdjoint

/-!
# The growing onsite commutator family on native trace GNS stages

The real weighted onsite recursion determines every operator. Algebraic bonding,
trace cyclicity, self-adjointness, and the uniform bound are proved, then fed to
the existing compatible-operator Hilbert-colimit construction. There is no
fixed-seed substitution or compatibility/boundedness premise.
-/
noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.GrowingOnsiteTraceGNSFamily

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredTracialGNSCommutatorTransport
open CuntzMatrixTowerInstantiation CuntzMatrixTraceTower
open CantorBernoulliCStarMatrixTraceState GrowingOnsiteMatrixHamiltonian GrowingOnsiteMatrixNorm
open FilteredCompatibleOperatorColimit FilteredIsometricHilbertCompletion

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

local notation "E" => GNSStage CStarMatrixStage cstarMatrixInductiveSystem cstarMatrixTraceStateFamily
local notation "S" => filteredGNSIsometricDirectSystem CStarMatrixStage
  cstarMatrixInductiveSystem cstarMatrixTraceStateFamily

/-- Cyclicity is proved from the actual normalized matrix trace. -/
theorem cstarTrace_cyclic (n : ℕ) (a b : CStarMatrixStage n) :
    (cstarMatrixTraceState n).functional (a * b) =
      (cstarMatrixTraceState n).functional (b * a) := by
  change matrixTraceState n (CStarMatrix.ofMatrixStarAlgEquiv.symm (a * b)) =
    matrixTraceState n (CStarMatrix.ofMatrixStarAlgEquiv.symm (b * a))
  rw [map_mul, map_mul]
  exact matrixTraceState_mul_comm n _ _

/-- The mapped onsite Hamiltonian is self-adjoint in the native C⋆ stage. -/
theorem cstarOnsite_selfAdjoint (w : ℕ → ℝ) (n : ℕ) :
    IsSelfAdjoint (cstarOnsiteHamiltonian w n) := by
  change star (CStarMatrix.ofMatrixStarAlgEquiv (onsiteHamiltonian w n) : CStarMatrixStage n) = _
  rw [← map_star]
  exact congrArg (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage n ≃⋆ₐ[ℂ] CStarMatrixStage n)
    (onsiteHamiltonian_isHermitian w n)

/-- Transport the actual all-index raw commutator theorem through the native equivalence. -/
theorem cstarOnsite_commutator_map (w : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j)
    (a : CStarMatrixStage i) :
    cstarOnsiteHamiltonian w j * cstarConcreteMap hij a -
        cstarConcreteMap hij a * cstarOnsiteHamiltonian w j =
      cstarConcreteMap hij (cstarOnsiteHamiltonian w i * a - a * cstarOnsiteHamiltonian w i) := by
  apply (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage j ≃⋆ₐ[ℂ] CStarMatrixStage j).symm.injective
  change onsiteHamiltonian w j *
      concreteMap hij ((CStarMatrix.ofMatrixStarAlgEquiv :
        MatrixStage i ≃⋆ₐ[ℂ] CStarMatrixStage i).symm a) -
      concreteMap hij ((CStarMatrix.ofMatrixStarAlgEquiv :
        MatrixStage i ≃⋆ₐ[ℂ] CStarMatrixStage i).symm a) * onsiteHamiltonian w j =
    concreteMap hij (onsiteHamiltonian w i *
      ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage i ≃⋆ₐ[ℂ] CStarMatrixStage i).symm a) -
      ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage i ≃⋆ₐ[ℂ] CStarMatrixStage i).symm a) *
        onsiteHamiltonian w i)
  exact onsite_commutator_concreteMap w hij
    ((CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage i ≃⋆ₐ[ℂ] CStarMatrixStage i).symm a)

/-- Actual growing commutator on the existing native trace-GNS stage. -/
def onsiteStageOperator (w : ℕ → ℝ) (n : ℕ) : E n →L[ℂ] E n :=
  (cstarMatrixTraceState n).functional.tracialCommutatorGNS (cstarTrace_cyclic n)
    (cstarOnsiteHamiltonian w n)

theorem onsiteStageOperator_selfAdjoint (w : ℕ → ℝ) (n : ℕ) :
    IsSelfAdjoint (onsiteStageOperator w n) :=
  (cstarMatrixTraceState n).functional.tracialCommutatorGNS_selfAdjoint
    (cstarTrace_cyclic n) (cstarOnsiteHamiltonian w n) (cstarOnsite_selfAdjoint w n)

/-- All-index GNS transport is derived, not assumed as a family field. -/
theorem onsiteStageOperator_transport (w : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) (x : E i) :
    (CStarStateColimit.Native.FilteredGNSHilbertColimit.filteredGNSIsometricDirectSystem
      CStarMatrixStage cstarMatrixInductiveSystem cstarMatrixTraceStateFamily).map hij (onsiteStageOperator w i x) = onsiteStageOperator w j ((CStarStateColimit.Native.FilteredGNSHilbertColimit.filteredGNSIsometricDirectSystem
      CStarMatrixStage cstarMatrixInductiveSystem cstarMatrixTraceStateFamily).map hij x) := by
  have he := commutator_transport CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily hij (cstarTrace_cyclic i) (cstarTrace_cyclic j)
    (cstarOnsiteHamiltonian w i) (cstarOnsiteHamiltonian w j)
    (cstarOnsite_commutator_map w hij)
  -- The native compatible family has state := cstarMatrixTraceState.
  -- Align its projected states with the concrete operators before evaluation.
  change (onsiteStageOperator w j).comp
      (filteredGNSMapCLM CStarMatrixStage cstarMatrixInductiveSystem
        cstarMatrixTraceStateFamily hij) =
    (filteredGNSMapCLM CStarMatrixStage cstarMatrixInductiveSystem
      cstarMatrixTraceStateFamily hij).comp (onsiteStageOperator w i) at he
  have hx := congrArg (fun T => T x) he
  simpa only [ContinuousLinearMap.comp_apply, filteredGNSMapCLM_apply,
    filteredGNSIsometricDirectSystem, filteredGNSLinearIsometry_apply]
    using hx.symm

theorem onsiteStageOperator_norm_le (w : ℕ → ℝ)
    (hw : Summable (fun j => |w j|)) (n : ℕ) :
    ‖onsiteStageOperator w n‖ ≤ 2 * ∑' j, |w j| := by
  exact ((cstarMatrixTraceState n).functional.tracialCommutatorGNS_norm_le
    (cstarTrace_cyclic n) (cstarOnsiteHamiltonian w n)).trans
    (mul_le_mul_of_nonneg_left (cstarOnsiteHamiltonian_norm_le_tsum w hw n) (by norm_num))

/-- Every field is derived from the onsite recursion, trace, and summability. -/
def onsiteCompatibleOperatorFamily (w : ℕ → ℝ) (hw : Summable (fun j => |w j|)) :
    CompatibleOperatorFamily E S where
  op := onsiteStageOperator w
  intertwines := onsiteStageOperator_transport w
  bound := 2 * ∑' j, |w j|
  norm_le := by
    intro n x
    exact ((onsiteStageOperator w n).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (onsiteStageOperator_norm_le w hw n) (norm_nonneg x))

/-- The genuine bounded operator on the existing completed filtered GNS colimit. -/
def onsiteCompletedOperator (w : ℕ → ℝ) (hw : Summable (fun j => |w j|)) :=
  completedOperator E S (onsiteCompatibleOperatorFamily w hw)

theorem onsiteCompletedOperator_selfAdjoint (w : ℕ → ℝ)
    (hw : Summable (fun j => |w j|)) : IsSelfAdjoint (onsiteCompletedOperator w hw) := by
  exact completedOperator_selfAdjoint E S (onsiteCompatibleOperatorFamily w hw)
    (onsiteStageOperator_selfAdjoint w)

/-- Actual finite-stage readback into the existing completed Hilbert colimit. -/
theorem onsiteCompletedOperator_stage (w : ℕ → ℝ)
    (hw : Summable (fun j => |w j|)) (n : ℕ) (x : E n) :
    onsiteCompletedOperator w hw (stageToHilbertDirectLimit E S n x) =
      stageToHilbertDirectLimit E S n (onsiteStageOperator w n x) :=
  completedOperator_stage E S (onsiteCompatibleOperatorFamily w hw) n x

end InfoGeometry.Canonical.GrowingOnsiteTraceGNSFamily

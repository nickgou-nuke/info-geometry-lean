import InfoGeometry.Clifford.Cl11GradingSl2
import InfoGeometry.Clifford.Cl11CompassMoritaBridge
import InfoGeometry.Clifford.Cl11TensorTower

namespace InfoGeometry.Canonical.Cl11StageOneMatrixBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11GradingSl2
open InfoGeometry.Clifford.Cl11CompassMoritaBridge

/-!
# Stage-one matrix bridge

This file connects the existing Clifford-algebra matrix equivalence with the
native first stage of the tensor tower.  It introduces no new carrier and
makes no claim about composition algebras or Bott periodicity.
-/

abbrev StageOne := MatStage 1

noncomputable def cl11ToStageOne :
    CliffordAlgebra q11 →ₐ[ℝ] StageOne :=
  Cl11CompassMoritaBridge.cl11EquivStageOne.toAlgHom

theorem cl11ToStageOne_eq_canonical :
    cl11ToStageOne =
      Cl11CompassMoritaBridge.cl11EquivStageOne.toAlgHom := by
  rfl

theorem cl11ToStageOne_apply (x : CliffordAlgebra q11) :
    TowerMatrix.matEquivFinPowTwo 1 (cl11ToStageOne x) =
      Cl11Matrix.cl11EquivMat x := by
  simpa [cl11ToStageOne, Cl11GradingSl2.clE] using
    (TowerMatrix.matEquivFinPowTwo 1).apply_symm_apply
      (Cl11Matrix.cl11EquivMat x)

theorem cl11ToStageOne_mul (x y : CliffordAlgebra q11) :
    cl11ToStageOne (x * y) = cl11ToStageOne x * cl11ToStageOne y := by
  exact (cl11ToStageOne).map_mul x y

theorem cl11ToStageOne_one :
    cl11ToStageOne (1 : CliffordAlgebra q11) = 1 := by
  exact (cl11ToStageOne).map_one

theorem clE_stageOne_readout :
    TowerMatrix.matEquivFinPowTwo 1
        (cl11ToStageOne Cl11GradingSl2.clE) =
      Cl11GradingSl2.E := by
  rw [cl11ToStageOne_apply]
  simp [Cl11GradingSl2.clE]

theorem clF_stageOne_readout :
    TowerMatrix.matEquivFinPowTwo 1
        (cl11ToStageOne Cl11GradingSl2.clF) =
      Cl11GradingSl2.F := by
  rw [cl11ToStageOne_apply]
  simp [Cl11GradingSl2.clF]

theorem clH_stageOne_readout :
    TowerMatrix.matEquivFinPowTwo 1
        (cl11ToStageOne Cl11GradingSl2.clH) =
      Cl11GradingSl2.H := by
  rw [cl11ToStageOne_apply]
  simp [Cl11GradingSl2.clH]

noncomputable def stageOneE : StageOne :=
  cl11ToStageOne Cl11GradingSl2.clE

noncomputable def stageOneF : StageOne :=
  cl11ToStageOne Cl11GradingSl2.clF

noncomputable def stageOneH : StageOne :=
  cl11ToStageOne Cl11GradingSl2.clH

theorem stageOne_bracket_H_E :
    ⁅stageOneH, stageOneE⁆ = (2 : ℝ) • stageOneE := by
  simpa [stageOneH, stageOneE, Ring.lie_def, map_sub, map_mul, map_smul] using
    congrArg cl11ToStageOne Cl11GradingSl2.cl_bracket_H_E

theorem stageOne_bracket_H_F :
    ⁅stageOneH, stageOneF⁆ = (-2 : ℝ) • stageOneF := by
  simpa [stageOneH, stageOneF, Ring.lie_def, map_sub, map_mul, map_smul] using
    congrArg cl11ToStageOne Cl11GradingSl2.cl_bracket_H_F

theorem stageOne_bracket_E_F :
    ⁅stageOneE, stageOneF⁆ = stageOneH := by
  simpa [stageOneE, stageOneF, stageOneH, Ring.lie_def, map_sub, map_mul] using
    congrArg cl11ToStageOne Cl11GradingSl2.cl_bracket_E_F

end InfoGeometry.Canonical.Cl11StageOneMatrixBridge

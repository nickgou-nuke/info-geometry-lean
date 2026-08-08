import Mathlib
import proofs.OperatorQGTSoldering
import InfoGeometry.Physics.BogoliubovPauliSolderedFrame
import InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Unified
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Physics.BogoliubovPauliSolderedFrame
open InfoGeometry.Optics.OperatorBogoliubovPauliBridge
open InfoGeometry.Optics.OperatorLiftCarrier

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommGroup W] [Module ℂ W]

noncomputable def qgtFromBogoliubov (bogoliubovState : UnifiedBogoliubovState (E := E)) : QGTFourVector W where
  symmetricBKM
  | 0 => algebraMap ℝ (Module.End ℂ W) ((bogoliubovState.2 0 0 + bogoliubovState.2 1 1) / 2)
  | 1 => algebraMap ℝ (Module.End ℂ W) ((bogoliubovState.2 0 1 + bogoliubovState.2 1 0) / 2)
  | 2 => 0
  | 3 => algebraMap ℝ (Module.End ℂ W) ((bogoliubovState.2 0 0 - bogoliubovState.2 1 1) / 2)
  antisymmetricBerry
  | 0 => 0
  | 1 => 0
  | 2 => algebraMap ℝ (Module.End ℂ W) ((bogoliubovState.2 0 1 - bogoliubovState.2 1 0) / 2)
  | 3 => 0

example (bogoliubovState : UnifiedBogoliubovState (E := E)) :
    QGTSoldering (qgtFromBogoliubov bogoliubovState) = 
    matrixAction (W := W) (complexifyMatrix bogoliubovState.2) := by
  dsimp [QGTSoldering, operatorSolderingAction]
  apply congrArg (matrixAction (W := W))
  ext i j x
  fin_cases i <;> fin_cases j <;>
  · dsimp only
    dsimp [QGTFourVector.totalOperator, complexifyMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.of_apply]
    simp [qgtFromBogoliubov, Module.algebraMap_end_apply]
    try simp only [smul_smul, Complex.I_mul_I]
    try simp only [neg_smul, one_smul, sub_neg_eq_add, ← sub_eq_add_neg]
    try simp only [← add_smul, ← sub_smul]
    congr 1
    ring

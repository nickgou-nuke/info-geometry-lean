import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Three-color operator braid transport into the sigma sectors

This owner keeps the braid action external: it acts on the coefficient
coordinates of `OperatorVector`, and the interaction with the native
`sigmaPlus`/`sigmaMinus` embeddings is proved by explicit intertwining
lemmas.

No claim is made that Zorn multiplication itself is braided.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.NCG

noncomputable section

variable {A : Type*} [Ring A]

/-- The cyclic permutation of the three operator coordinates. -/
def operatorCycle : Fin 3 ≃ Fin 3 where
  toFun
    | 0 => 1
    | 1 => 2
    | 2 => 0
  invFun
    | 0 => 2
    | 1 => 0
    | 2 => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- The transported operator vector along the cyclic colour action. -/
def operatorCycleVec (U : OperatorVector A) : OperatorVector A :=
  fun i => U (operatorCycle.symm i)

@[simp] theorem operatorCycleVec_apply (U : OperatorVector A) (i : Fin 3) :
    operatorCycleVec U i = U (operatorCycle.symm i) := rfl

/-- The cyclic action is of order three on the index set. -/
theorem operatorCycle_three :
    operatorCycle.trans (operatorCycle.trans operatorCycle) =
      Equiv.refl (Fin 3) := by
  ext i
  fin_cases i <;> rfl

/-- The cyclic action preserves the operator cross product. -/
theorem operatorCycle_cross (U V : OperatorVector A) :
    operatorCycleVec (operatorCross U V) =
      operatorCross (operatorCycleVec U) (operatorCycleVec V) := by
  funext i
  fin_cases i <;> simp [operatorCycleVec, operatorCross,
    NCZornElement.zornCross, operatorCycle]

/-- The cyclic action preserves the operator dot product. -/
theorem operatorCycle_dot (U V : OperatorVector A) :
    operatorDot (operatorCycleVec U) (operatorCycleVec V) =
      operatorDot U V := by
  simp [operatorCycleVec, operatorDot, NCZornElement.zornDot, operatorCycle]
  ac_rfl

/-- Transport of the `sigmaPlus` sector through the cyclic colour action. -/
theorem sigmaPlus_cycle_intertwines (U V : OperatorVector A) :
    operatorZornMul (sigmaPlus (operatorCycleVec U))
        (sigmaPlus (operatorCycleVec V)) =
      sigmaMinus (operatorCycleVec (operatorCross U V)) := by
  simpa [operatorCycle_cross] using
    (sigmaPlus_mul_sigmaPlus (U := operatorCycleVec U) (V := operatorCycleVec V))

/-- Transport of the `sigmaMinus` sector through the cyclic colour action. -/
theorem sigmaMinus_cycle_intertwines (U V : OperatorVector A) :
    operatorZornMul (sigmaMinus (operatorCycleVec U))
        (sigmaMinus (operatorCycleVec V)) =
      sigmaPlus (-operatorCycleVec (operatorCross U V)) := by
  simpa [operatorCycle_cross] using
    (sigmaMinus_mul_sigmaMinus (U := operatorCycleVec U) (V := operatorCycleVec V))

/-- Mixed-sector transport remains compatible with the cyclic colour action. -/
theorem sigmaPlus_sigmaMinus_cycle_intertwines (U V : OperatorVector A) :
    operatorZornMul (sigmaPlus (operatorCycleVec U))
        (sigmaMinus (operatorCycleVec V)) =
      nPlus (operatorDot (operatorCycleVec U) (operatorCycleVec V)) := by
  simpa [operatorCycle_dot] using
    (sigmaPlus_mul_sigmaMinus (U := operatorCycleVec U) (V := operatorCycleVec V))

/-- Mixed-sector transport remains compatible with the cyclic colour action. -/
theorem sigmaMinus_sigmaPlus_cycle_intertwines (U V : OperatorVector A) :
    operatorZornMul (sigmaMinus (operatorCycleVec U))
        (sigmaPlus (operatorCycleVec V)) =
      nMinus (operatorDot (operatorCycleVec U) (operatorCycleVec V)) := by
  simpa [operatorCycle_dot] using
    (sigmaMinus_mul_sigmaPlus (U := operatorCycleVec U) (V := operatorCycleVec V))

end
end InfoGeometry.Canonical

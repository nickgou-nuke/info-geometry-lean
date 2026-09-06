import Mathlib
import InfoGeometry.Algebra.ChiralOperatorTopologicalBridge
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator

/-!
# Topological product-carrier realization of operator-valued Zorn multiplication

`NCZornElement` remains the algebraic owner and has no topology.  This file
defines the same displayed multiplication on its finite product presentation
`(n₊, n₋, s₊, s₋)`, where Mathlib supplies the product topology.  The result is
only a continuous binary operation; no associativity or algebra structure is
claimed.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

def operatorSageTopologicalMul
    (X Y : OperatorSageTopologicalCarrier A) :
    OperatorSageTopologicalCarrier A :=
  (X.1 * Y.1 + operatorDot X.2.2.1 Y.2.2.2,
    X.2.1 * Y.2.1 + operatorDot X.2.2.2 Y.2.2.1,
    (fun c => X.1 * Y.2.2.1 c + X.2.2.1 c * Y.2.1 -
      operatorCross X.2.2.2 Y.2.2.2 c),
    (fun c => X.2.1 * Y.2.2.2 c + X.2.2.2 c * Y.1 +
      operatorCross X.2.2.1 Y.2.2.1 c))

theorem operatorSageTopologicalMul_toZorn
    (X Y : OperatorSageTopologicalCarrier A) :
    operatorSageTopologicalToZorn (operatorSageTopologicalMul X Y) =
      operatorZornMul (operatorSageTopologicalToZorn X)
        (operatorSageTopologicalToZorn Y) := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext c
    rfl
  · funext c
    rfl

theorem continuous_operatorSageTopologicalMul :
    Continuous (fun p : OperatorSageTopologicalCarrier A ×
      OperatorSageTopologicalCarrier A =>
      operatorSageTopologicalMul p.1 p.2) := by
  unfold operatorSageTopologicalMul
  have hPlus : Continuous (fun p :
      OperatorSageTopologicalCarrier A × OperatorSageTopologicalCarrier A =>
      p.1.1 * p.2.1 + operatorDot p.1.2.2.1 p.2.2.2.2) := by
    change Continuous (fun p :
      OperatorSageTopologicalCarrier A × OperatorSageTopologicalCarrier A =>
      p.1.1 * p.2.1 +
        (p.1.2.2.1 0 * p.2.2.2.2 0 +
          p.1.2.2.1 1 * p.2.2.2.2 1 +
          p.1.2.2.1 2 * p.2.2.2.2 2))
    fun_prop
  have hMinus : Continuous (fun p :
      OperatorSageTopologicalCarrier A × OperatorSageTopologicalCarrier A =>
      p.1.2.1 * p.2.2.1 + operatorDot p.1.2.2.2 p.2.2.2.1) := by
    change Continuous (fun p :
      OperatorSageTopologicalCarrier A × OperatorSageTopologicalCarrier A =>
      p.1.2.1 * p.2.2.1 +
        (p.1.2.2.2 0 * p.2.2.2.1 0 +
          p.1.2.2.2 1 * p.2.2.2.1 1 +
          p.1.2.2.2 2 * p.2.2.2.1 2))
    fun_prop
  have hSigmaPlus : Continuous (fun p :
      OperatorSageTopologicalCarrier A × OperatorSageTopologicalCarrier A =>
      (fun c => p.1.1 * p.2.2.2.1 c + p.1.2.2.1 c * p.2.2.1 -
        operatorCross p.1.2.2.2 p.2.2.2.2 c)) := by
    apply continuous_pi
    intro c
    fin_cases c <;>
      simp [operatorCross, NCZornElement.zornCross] <;>
      fun_prop
  have hSigmaMinus : Continuous (fun p :
      OperatorSageTopologicalCarrier A × OperatorSageTopologicalCarrier A =>
      (fun c => p.1.2.1 * p.2.2.2.2 c + p.1.2.2.2 c * p.2.1 +
        operatorCross p.1.2.2.1 p.2.2.2.1 c)) := by
    apply continuous_pi
    intro c
    fin_cases c <;>
      simp [operatorCross, NCZornElement.zornCross] <;>
      fun_prop
  exact hPlus.prodMk (hMinus.prodMk (hSigmaPlus.prodMk hSigmaMinus))

def operatorSageTopologicalCommutator
    (X Y : OperatorSageTopologicalCarrier A) :
    OperatorSageTopologicalCarrier A :=
  operatorSageTopologicalMul X Y - operatorSageTopologicalMul Y X

theorem continuous_operatorSageTopologicalCommutator :
    Continuous (fun p : OperatorSageTopologicalCarrier A ×
      OperatorSageTopologicalCarrier A =>
      operatorSageTopologicalCommutator p.1 p.2) := by
  unfold operatorSageTopologicalCommutator
  exact (continuous_operatorSageTopologicalMul.comp
      (continuous_fst.prodMk continuous_snd)).sub
    (continuous_operatorSageTopologicalMul.comp
      (continuous_snd.prodMk continuous_fst))

@[simp] theorem operatorSageTopologicalCommutator_self
    (X : OperatorSageTopologicalCarrier A) :
    operatorSageTopologicalCommutator X X = 0 := by
  simp [operatorSageTopologicalCommutator]

end
end InfoGeometry.Topology

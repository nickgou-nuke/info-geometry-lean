import InfoGeometry.Quantum.NeutralKreinMajoranaFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native causal--entropy axes on the real doubled carrier

The canonical finite neutral frame already contains two real involutions:
`grading` and `exchange`.  This file records their genuine algebraic packet.
Their product is the internal complex structure (up to the established sign
of `majoranaForm`); no complex scalar extension is used.
-/

namespace InfoGeometry.Projective.SplitQuaternionCausalEntropyAxes

open Matrix
open InfoGeometry.Quantum.NeutralKreinMajoranaFrame

abbrev Mat4R := InfoGeometry.Quantum.NeutralKreinMajoranaFrame.DoubledMat4R

def causalAxis : Mat4R := grading 2

def entropyAxis : Mat4R := exchange 2

def internalComplex : Mat4R := causalAxis * entropyAxis

theorem causalAxis_sq : causalAxis * causalAxis = (1 : Mat4R) := by
  exact grading_sq 2

theorem entropyAxis_sq : entropyAxis * entropyAxis = (1 : Mat4R) := by
  exact exchange_sq 2

theorem causalEntropy_anticommute :
    causalAxis * entropyAxis = -(entropyAxis * causalAxis) := by
  exact grading_exchange_anticommute 2

theorem internalComplex_sq :
    internalComplex * internalComplex = -(1 : Mat4R) := by
  have h : entropyAxis * causalAxis = -(causalAxis * entropyAxis) := by
    have h' := congrArg Neg.neg causalEntropy_anticommute
    simpa using h'.symm
  calc
    internalComplex * internalComplex =
        causalAxis * (entropyAxis * causalAxis) * entropyAxis := by
          simp [internalComplex, Matrix.mul_assoc]
    _ = causalAxis * (-(causalAxis * entropyAxis)) * entropyAxis := by
          rw [h]
    _ = -((causalAxis * causalAxis) * (entropyAxis * entropyAxis)) := by
          simp [Matrix.mul_assoc]
    _ = -(1 : Mat4R) := by rw [causalAxis_sq, entropyAxis_sq]; simp

theorem internalComplex_eq_majorana :
    internalComplex = majoranaForm 2 := by
  unfold internalComplex causalAxis entropyAxis grading exchange majoranaForm
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem causalAxis_anti_isometry :
    causalAxis.transpose * kreinMetric 2 * causalAxis = -(kreinMetric 2) := by
  exact kreinMetric_grading_anti_isometry 2

theorem entropyAxis_isometry :
    entropyAxis.transpose * kreinMetric 2 * entropyAxis = kreinMetric 2 := by
  unfold entropyAxis kreinMetric exchange
  rw [Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

end InfoGeometry.Projective.SplitQuaternionCausalEntropyAxes

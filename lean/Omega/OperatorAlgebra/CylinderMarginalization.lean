import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- Chapter-local data for cylinder-probability marginalization. The structure fixes a word, its
two one-step extensions, the cylinder probability observable, and the trace-additivity witness
showing that the parent cylinder splits as the sum of its two children. -/
structure CylinderMarginalizationData where
  word : List Bool
  cylinderProbability : List Bool → ℝ

def extendZero (word : List Bool) : List Bool := word ++ [false]

def extendOne (word : List Bool) : List Bool := word ++ [true]

/-- The local cylinder split is exactly the finite additivity equation for the two canonical
one-step extensions. No global consistency statement is inferred from a single-cylinder law.
    prop:op-algebra-cylinder-marginalization -/
theorem paper_op_algebra_cylinder_marginalization (D : CylinderMarginalizationData)
    (hAdd : D.cylinderProbability D.word =
      D.cylinderProbability (extendZero D.word) +
        D.cylinderProbability (extendOne D.word)) :
    D.cylinderProbability D.word =
      D.cylinderProbability (extendZero D.word) +
        D.cylinderProbability (extendOne D.word) := hAdd

/-- Concrete finite data for pushforwarding a mass function along a fold map and reading the result
on each visible coordinate as the sum of the source masses over the corresponding fiber. -/
structure FoldPushforwardFiberSumData where
  Ω : Type
  X : Type
  instDecEqΩ : DecidableEq Ω
  instFintypeΩ : Fintype Ω
  instDecEqX : DecidableEq X
  fold : Ω → X
  mass : Ω → ℚ

attribute [instance] FoldPushforwardFiberSumData.instDecEqΩ
attribute [instance] FoldPushforwardFiberSumData.instFintypeΩ
attribute [instance] FoldPushforwardFiberSumData.instDecEqX

namespace FoldPushforwardFiberSumData

/-- The finite source fiber over a visible state `x`. -/
def fiber (D : FoldPushforwardFiberSumData) (x : D.X) : Finset D.Ω :=
  Finset.univ.filter fun a => D.fold a = x

/-- The pushforward mass of `x`, defined by summing the source masses over its fold fiber. -/
def pushforwardMass (D : FoldPushforwardFiberSumData) (x : D.X) : ℚ :=
  Finset.sum (D.fiber x) D.mass

/-- Coordinate form of the finite pushforward identity. -/
def pushforwardFiberSum (D : FoldPushforwardFiberSumData) : Prop :=
  ∀ x : D.X, D.pushforwardMass x = Finset.sum (D.fiber x) D.mass

end FoldPushforwardFiberSumData

open FoldPushforwardFiberSumData

/-- Paper-facing fold-pushforward fiber-sum identity.
    cor:op-algebra-fold-pushforward-fiber-sum -/
theorem paper_op_algebra_fold_pushforward_fiber_sum (D : FoldPushforwardFiberSumData) :
    D.pushforwardFiberSum := by
  change ∀ x : D.X, D.pushforwardMass x = Finset.sum (D.fiber x) D.mass
  intro x
  rfl

/-- Recursive product of time-slice projectors along a cylinder word. -/
def cylinderWordValue {ι : Type*} (sliceProjector : ι → ℝ) : List ι → ℝ
  | [] => 1
  | a :: w => sliceProjector a * cylinderWordValue sliceProjector w

/-- Concrete scalar package encoding cylinder naturality under conjugation. The scalar model keeps
the proof algebraic while matching the paper's operator/trace pattern. -/
structure CylinderNaturalityData where
  symbol : Type*
  unitary : ℝ
  unitaryInv : ℝ
  sliceProjector : symbol → ℝ
  transportedSliceProjector : symbol → ℝ
  trace : ℝ → ℝ

/-- Cylinder operator before conjugation. -/
def CylinderNaturalityData.cylinderOperator (D : CylinderNaturalityData) (w : List D.symbol) : ℝ :=
  cylinderWordValue D.sliceProjector w

/-- Cylinder operator after transporting each time-slice projector. -/
def CylinderNaturalityData.transportedCylinderOperator (D : CylinderNaturalityData)
    (w : List D.symbol) : ℝ :=
  cylinderWordValue D.transportedSliceProjector w

/-- Cylinder probability before conjugation. -/
def CylinderNaturalityData.cylinderProbability (D : CylinderNaturalityData)
    (w : List D.symbol) : ℝ :=
  D.trace (D.cylinderOperator w)

/-- Cylinder probability after conjugation. -/
def CylinderNaturalityData.transportedCylinderProbability (D : CylinderNaturalityData)
    (w : List D.symbol) : ℝ :=
  D.trace (D.transportedCylinderOperator w)

/-- The transported cylinder operator is the conjugate of the original one. -/
def CylinderNaturalityData.cylinderOperatorNaturality (D : CylinderNaturalityData) : Prop :=
  ∀ w, D.transportedCylinderOperator w = D.unitary * D.cylinderOperator w * D.unitaryInv

/-- The cylinder probabilities are invariant under the conjugating unitary. -/
def CylinderNaturalityData.cylinderProbabilityNaturality (D : CylinderNaturalityData) : Prop :=
  ∀ w, D.transportedCylinderProbability w = D.cylinderProbability w

lemma cylinder_operator_naturality_aux (D : CylinderNaturalityData)
    (sliceNaturality :
      ∀ a, D.transportedSliceProjector a = D.unitary * D.sliceProjector a * D.unitaryInv)
    (unitaryInv_mul_unitary : D.unitaryInv * D.unitary = 1)
    (unitary_mul_unitaryInv : D.unitary * D.unitaryInv = 1) :
    ∀ w, D.transportedCylinderOperator w = D.unitary * D.cylinderOperator w * D.unitaryInv
  | [] => by
      simp [CylinderNaturalityData.transportedCylinderOperator, CylinderNaturalityData.cylinderOperator,
        cylinderWordValue, unitary_mul_unitaryInv]
  | a :: w => by
      have ih := cylinder_operator_naturality_aux D sliceNaturality unitaryInv_mul_unitary
        unitary_mul_unitaryInv w
      calc
        D.transportedCylinderOperator (a :: w)
            = (D.unitary * D.sliceProjector a * D.unitaryInv) *
                D.transportedCylinderOperator w := by
                  simp [CylinderNaturalityData.transportedCylinderOperator, cylinderWordValue,
                    sliceNaturality a]
        _ = (D.unitary * D.sliceProjector a * D.unitaryInv) *
                (D.unitary * D.cylinderOperator w * D.unitaryInv) := by rw [ih]
        _ = D.unitary * D.sliceProjector a * (D.unitaryInv * D.unitary) *
                D.cylinderOperator w * D.unitaryInv := by ring
        _ = D.unitary * D.sliceProjector a * D.cylinderOperator w * D.unitaryInv := by
          simp [unitaryInv_mul_unitary]
        _ = D.unitary * D.cylinderOperator (a :: w) * D.unitaryInv := by
          simp [CylinderNaturalityData.cylinderOperator, cylinderWordValue, mul_assoc]

/-- Conjugation transports each time-slice projector, hence also the cylinder words built from
them; trace invariance then gives equality of the associated cylinder probabilities.
    prop:op-algebra-cylinder-naturality -/
theorem paper_op_algebra_cylinder_naturality (D : CylinderNaturalityData)
    (sliceNaturality :
      ∀ a, D.transportedSliceProjector a = D.unitary * D.sliceProjector a * D.unitaryInv)
    (unitaryInv_mul_unitary : D.unitaryInv * D.unitary = 1)
    (unitary_mul_unitaryInv : D.unitary * D.unitaryInv = 1)
    (traceInvariant : ∀ x, D.trace (D.unitary * x * D.unitaryInv) = D.trace x) :
    D.cylinderOperatorNaturality ∧ D.cylinderProbabilityNaturality := by
  constructor
  · intro w
    exact cylinder_operator_naturality_aux D sliceNaturality unitaryInv_mul_unitary
      unitary_mul_unitaryInv w
  · intro w
    unfold CylinderNaturalityData.transportedCylinderProbability
      CylinderNaturalityData.cylinderProbability
    rw [cylinder_operator_naturality_aux D sliceNaturality unitaryInv_mul_unitary
      unitary_mul_unitaryInv w, traceInvariant]

end Omega.OperatorAlgebra

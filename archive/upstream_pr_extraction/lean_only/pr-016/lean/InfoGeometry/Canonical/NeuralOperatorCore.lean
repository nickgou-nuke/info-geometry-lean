import InfoGeometry.Meta.Architecture
import Mathlib.Data.Real.Basic

/-!
# InfoGeometry.Canonical.NeuralOperatorCore

Owner contracts for function-to-function approximation on operator lanes.

This file keeps approximation obligations in information-geometric
shape/scale-cost form and avoids least-squares-only contracts.
-/

namespace InfoGeometry.Canonical.NeuralOperatorCore

universe u v w

/-- Function-to-function neural operator surface. -/
@[rep_depth operator]
abbrev NeuralOperator (X : Type u) (Y : Type v) (Z : Type w) : Type (max u v w) :=
  (X → Y) → (X → Z)

/--
Shape/scale information-cost package on output function space.

This is the canonical contract surface for approximation control in this module.
-/
@[rep_depth operator]
structure ShapeScaleCost (X : Type u) (Z : Type w) where
  shapeTerm : (X → Z) → (X → Z) → ℝ
  scaleTerm : (X → Z) → (X → Z) → ℝ
  shape_nonneg : ∀ f g : X → Z, 0 ≤ shapeTerm f g
  scale_nonneg : ∀ f g : X → Z, 0 ≤ scaleTerm f g

namespace ShapeScaleCost

/-- Total information cost as shape + scale terms. -/
@[rep_depth operator]
noncomputable def totalCost
    {X : Type u} {Z : Type w}
    (C : ShapeScaleCost X Z)
    (f g : X → Z) : ℝ :=
  C.shapeTerm f g + C.scaleTerm f g

/-- Nonnegativity of total information cost. -/
@[rep_depth operator]
theorem totalCost_nonneg
    {X : Type u} {Z : Type w}
    (C : ShapeScaleCost X Z)
    (f g : X → Z) :
    0 ≤ C.totalCost f g := by
  unfold totalCost
  exact add_nonneg (C.shape_nonneg f g) (C.scale_nonneg f g)

end ShapeScaleCost

/--
Pointwise-on-domain approximation contract for a function-to-function operator.

`costBound` certifies a uniform shape/scale bound on the declared domain.
-/
@[rep_depth operator]
structure NeuralOperatorApproximationContract
    {X : Type u} {Y : Type v} {Z : Type w}
    (N : NeuralOperator X Y Z) where
  target : NeuralOperator X Y Z
  costModel : ShapeScaleCost X Z
  domain : (X → Y) → Prop
  costBound : ℝ
  costBound_nonneg : 0 ≤ costBound
  pointwise_cost_le :
    ∀ input : X → Y, domain input →
      costModel.totalCost (N input) (target input) ≤ costBound

/-- Contract projection: nonnegativity of the certified bound. -/
@[rep_depth operator]
theorem costBound_nonneg
    {X : Type u} {Y : Type v} {Z : Type w}
    {N : NeuralOperator X Y Z}
    (C : NeuralOperatorApproximationContract N) :
    0 ≤ C.costBound :=
  C.costBound_nonneg

/-- Contract projection: operator output cost bound on the declared domain. -/
@[rep_depth operator]
theorem operator_totalCost_le_of_contract
    {X : Type u} {Y : Type v} {Z : Type w}
    {N : NeuralOperator X Y Z}
    (C : NeuralOperatorApproximationContract N)
    {input : X → Y} (hinput : C.domain input) :
    C.costModel.totalCost (N input) (C.target input) ≤ C.costBound :=
  C.pointwise_cost_le input hinput

/-- Pointwise scalar readout discrepancy between two output functions. -/
@[rep_depth operator]
noncomputable def pointwiseReadoutError
    {X : Type u} {Z : Type w}
    (readout : Z → ℝ) (x : X) (f g : X → Z) : ℝ :=
  abs (readout (f x) - readout (g x))

/-- Readout discrepancy is always nonnegative. -/
@[rep_depth operator]
theorem pointwiseReadoutError_nonneg
    {X : Type u} {Z : Type w}
    (readout : Z → ℝ) (x : X) (f g : X → Z) :
    0 ≤ pointwiseReadoutError readout x f g := by
  unfold pointwiseReadoutError
  exact abs_nonneg _

/--
Readout-level bridge: if readout discrepancy is dominated by shape/scale cost,
the same contract bound controls pointwise readout error.
-/
@[rep_depth operator]
theorem pointwiseReadoutError_le_of_contract
    {X : Type u} {Y : Type v} {Z : Type w}
    {N : NeuralOperator X Y Z}
    (C : NeuralOperatorApproximationContract N)
    (readout : Z → ℝ)
    (hdom : ∀ f g : X → Z, ∀ x : X,
      pointwiseReadoutError readout x f g ≤ C.costModel.totalCost f g)
    {input : X → Y} (hinput : C.domain input)
    (x : X) :
    pointwiseReadoutError readout x (N input) (C.target input) ≤ C.costBound := by
  calc
    pointwiseReadoutError readout x (N input) (C.target input)
        ≤ C.costModel.totalCost (N input) (C.target input) := hdom _ _ x
    _ ≤ C.costBound := C.pointwise_cost_le input hinput

/--
Existence wrapper for approximation at tolerance `ε`.

This is an owner-level theorem surface; it does not assert existence on its own.
-/
@[rep_depth operator]
def HasNeuralOperatorApproximationAt
    {X : Type u} {Y : Type v} {Z : Type w}
    (N : NeuralOperator X Y Z) (ε : ℝ) : Prop :=
  ∃ C : NeuralOperatorApproximationContract N, C.costBound ≤ ε

end InfoGeometry.Canonical.NeuralOperatorCore

import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ArnoldApproximationCore

Owner contracts for approximation claims on the Arnold-Majorana generator lane.

This file deliberately avoids a global universal-approximation statement. It
packages only pointwise-on-domain error contracts that can be consumed by
downstream presentation/intertwiner lanes without introducing vacuous
hypotheses.
-/

namespace ArnoldApproximationCore

open InfoGeometry.Canonical.MoE

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/--
Canonical information-geometric shape/scale cost package on the Arnold carrier.

This keeps approximation contracts in divergence language (shape + scale) rather
than least-squares language.
-/
@[rep_depth operator]
structure ArnoldShapeScaleCost where
  shapeTerm : ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E → ℝ
  scaleTerm : ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E → ℝ
  shape_nonneg : ∀ x y, 0 ≤ shapeTerm x y
  scale_nonneg : ∀ x y, 0 ≤ scaleTerm x y

namespace ArnoldShapeScaleCost

/-- Total information cost as shape + scale terms. -/
@[rep_depth operator]
noncomputable def totalCost
    (C : ArnoldShapeScaleCost (E := E))
    (x y : ArnoldMajoranaCarrier E) : ℝ :=
  C.shapeTerm x y + C.scaleTerm x y

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
@[rep_depth operator]
theorem totalCost_nonneg
    (C : ArnoldShapeScaleCost (E := E))
    (x y : ArnoldMajoranaCarrier E) :
    0 ≤ C.totalCost x y := by
  unfold totalCost
  linarith [C.shape_nonneg x y, C.scale_nonneg x y]

end ArnoldShapeScaleCost

/--
Pointwise approximation contract for the one-token Arnold generator lane.

`costBound` is a certified uniform bound over the declared `domain`, measured
by an explicitly supplied information-geometric shape/scale cost.
-/
@[rep_depth operator]
structure ArnoldGeneratorApproximationContract
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) where
  target : ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E
  costModel : ArnoldShapeScaleCost (E := E)
  domain : Set (ArnoldMajoranaCarrier E)
  costBound : ℝ
  costBound_nonneg : 0 ≤ costBound
  pointwise_cost_le :
    ∀ ψ, ψ ∈ domain →
      costModel.totalCost
          (arnoldNetworkOutput n net β (fun _ : Unit => ψ) ())
          (target ψ) ≤ costBound

/-- Contract projection: nonnegativity of the certified cost bound. -/
@[rep_depth operator]
theorem costBound_nonneg
    {n : Nat} {net : ArnoldMajoranaNetwork n E} {β : ℝ}
    (C : ArnoldGeneratorApproximationContract (E := E) n net β) :
    0 ≤ C.costBound :=
  C.costBound_nonneg

/-- Contract projection: pointwise cost bound on any state inside the contract domain. -/
@[rep_depth operator]
theorem arnoldGeneratorCost_le
    {n : Nat} {net : ArnoldMajoranaNetwork n E} {β : ℝ}
    (C : ArnoldGeneratorApproximationContract (E := E) n net β)
    {ψ : ArnoldMajoranaCarrier E} (hψ : ψ ∈ C.domain) :
    C.costModel.totalCost
      (arnoldNetworkOutput n net β (fun _ : Unit => ψ) ())
      (C.target ψ) ≤ C.costBound :=
  C.pointwise_cost_le ψ hψ

/-- Contract projection: pointwise shape-term nonnegativity. -/
@[rep_depth operator]
theorem arnoldGeneratorShapeCost_nonneg
    {n : Nat} {net : ArnoldMajoranaNetwork n E} {β : ℝ}
    (C : ArnoldGeneratorApproximationContract (E := E) n net β)
    (x y : ArnoldMajoranaCarrier E) :
    0 ≤ C.costModel.shapeTerm x y :=
  C.costModel.shape_nonneg x y

/-- Contract projection: pointwise scale-term nonnegativity. -/
@[rep_depth operator]
theorem arnoldGeneratorScaleCost_nonneg
    {n : Nat} {net : ArnoldMajoranaNetwork n E} {β : ℝ}
    (C : ArnoldGeneratorApproximationContract (E := E) n net β)
    (x y : ArnoldMajoranaCarrier E) :
    0 ≤ C.costModel.scaleTerm x y :=
  C.costModel.scale_nonneg x y

/--
Readout-level skeleton: the norm readout of Arnold output is controlled by the
same cost bound when the supplied cost dominates readout differences.
-/
@[rep_depth operator]
theorem metricReadout_error_le_of_contract
    {n : Nat} {net : ArnoldMajoranaNetwork n E} {β : ℝ}
    (C : ArnoldGeneratorApproximationContract (E := E) n net β)
    (hdom : ∀ x y : ArnoldMajoranaCarrier E, |‖x‖ - ‖y‖| ≤ C.costModel.totalCost x y)
    {ψ : ArnoldMajoranaCarrier E} (hψ : ψ ∈ C.domain) :
    |‖arnoldNetworkOutput n net β (fun _ : Unit => ψ) ()‖ - ‖C.target ψ‖| ≤ C.costBound := by
  exact le_trans (hdom _ _) (C.pointwise_cost_le ψ hψ)

/--
Existence wrapper for approximation claims at tolerance `ε`.

This is an owner-level theorem surface used by downstream adapters; it does not
assert existence by itself.
-/
@[rep_depth operator]
def HasArnoldApproximationAt
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β ε : ℝ) : Prop :=
  ∃ C : ArnoldGeneratorApproximationContract (E := E) n net β,
    C.costBound ≤ ε

end ArnoldApproximationCore

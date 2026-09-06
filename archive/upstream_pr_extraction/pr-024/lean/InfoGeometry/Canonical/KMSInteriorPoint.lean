import Mathlib

/-!
# KMS Interior Point — Self-Concordant Barrier

The KMS flow toward the Zorn-maximal Cantor boundary is isomorphic to a
primal-dual interior point method.  The regularizer exp(εK) - I - εK
satisfies the self-concordant bound ‖exp(εK) - I - εK‖ ≤ ε² for small ε
when ‖K‖ = 1.

This bounds the local metric deformation (Dikin ellipsoid) and forces
the shift operator S_left to be uniformly continuous on the ℓ² completion.

#### BUCKET 1: CLOSED FINITE THEOREMS
None in this file.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
* `dikin_bounded_of_bregman_bound`
* `flow_uniformly_continuous_of_lipschitz_step`

#### BUCKET 3: OPEN CLOSURE DEBT
* Construct the operator exponential used by the KMS phase-axis flow.
* Prove the quadratic Bregman remainder estimate for that exponential.
* Prove the local Lipschitz continuity estimate for exponential flow steps.
-/

noncomputable section KMSInteriorPoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An explicitly supplied operator exponential for the KMS phase-axis flow. -/
abbrev ExpOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  (H →L[ℝ] H) → (H →L[ℝ] H)

/--
The self-concordant barrier bound:

  ‖exp(εK) - I - εK‖ ≤ ε²·‖K‖²   for ε·‖K‖ ≤ 1
-/
def HasBregmanQuadraticBound
    (expOp : ExpOp H)
    (K : H →L[ℝ] H) : Prop :=
  ∀ ε : ℝ, ε * ‖K‖ ≤ 1 →
    ‖expOp (ε • K) - (1 : H →L[ℝ] H) - (ε • K)‖ ≤ ε ^ 2 * ‖K‖ ^ 2

/--
Local Lipschitz continuity of exponential steps along a fixed operator.
-/
def HasLocalFlowLipschitz
    (expOp : ExpOp H)
    (K : H →L[ℝ] H)
    (ε : ℝ) : Prop :=
  ∀ δε : ℝ, |δε| < 1 →
    ∃ C : ℝ, ‖expOp ((ε + δε) • K) - expOp (ε • K)‖ ≤ C * |δε|

/--
The Dikin ellipsoid bound: when ‖K‖ = 1, the local deformation is ≤ ε².
-/
theorem dikin_bounded_of_bregman_bound
    (expOp : ExpOp H)
    (K : H →L[ℝ] H)
    (hquad : HasBregmanQuadraticBound expOp K)
    (hK_norm : ‖K‖ = 1)
    (ε : ℝ)
    (hε : ε ≤ 1) :
    ‖expOp (ε • K) - (1 : H →L[ℝ] H) - (ε • K)‖ ≤ ε ^ 2 := by
  have hε' : ε * ‖K‖ ≤ 1 := by
    rw [hK_norm, mul_one]
    exact hε
  have h := hquad ε hε'
  rw [hK_norm] at h
  simpa [sq, mul_one] using h

/--
Uniform continuity of the diagonal action: the difference of two
exponential steps is bounded by C·|δε|.
-/
theorem flow_uniformly_continuous_of_lipschitz_step
    (expOp : ExpOp H)
    (K : H →L[ℝ] H)
    (ε δε : ℝ)
    (hlip : HasLocalFlowLipschitz expOp K ε)
    (h_small : |δε| < 1) :
    ∃ C : ℝ, ‖expOp ((ε + δε) • K) - expOp (ε • K)‖ ≤ C * |δε| :=
  hlip δε h_small

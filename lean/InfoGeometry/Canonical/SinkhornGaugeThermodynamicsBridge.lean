import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.SinkhornKMSCore

/-!
# InfoGeometry.Canonical.SinkhornGaugeThermodynamicsBridge

Finite Sinkhorn transport as Weyl-gauge thermodynamics.

This bridge formalizes only the source-backed part of the gauge/stat-mechanics
analogy:

- row and column Sinkhorn normalization are diagonal Weyl gauge scalings,
- the RN barrier is the finite thermodynamic force/readout budget,
- one-step barrier monotonicity supplies the available defect budget,
- KMS residual control consumes that budget.

It does not claim that chemical potential is already a Bogoliubov gauge field.
That is a later grand-canonical/background-field bridge.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.SinkhornGaugeThermodynamicsBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.KMSSinkhornBridge

section FiniteGaugeThermodynamics

variable (n : Nat)

/--
Row normalization is a left diagonal Weyl-gauge transform by inverse row-count
carriers.
-/
@[rep_depth transport, capstone]
theorem rowNormalization_is_leftWeylGauge
    (M : SinkhornMatrix n)
    (hrow : HasPositiveRowSums n M) :
    rowNormalize n M hrow = Matrix.diagonal (leftWeylScale n M) * M :=
  rowNormalize_eq_leftDiagonalGauge (n := n) M hrow

/--
Column normalization is a right diagonal Weyl-gauge transform by inverse
column-count carriers.
-/
@[rep_depth transport, capstone]
theorem colNormalization_is_rightWeylGauge
    (M : SinkhornMatrix n)
    (hcol : HasPositiveColSums n M) :
    colNormalize n M hcol = M * Matrix.diagonal (rightWeylScale n M) :=
  colNormalize_eq_rightDiagonalGauge (n := n) M hcol

/--
Two-step Sinkhorn balancing is exactly a two-sided diagonal Weyl-gauge
transform.
-/
@[rep_depth transport, capstone]
theorem sinkhornTwoStep_is_twoSidedWeylGauge
    (M : SinkhornMatrix n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      =
    Matrix.diagonal (leftWeylScale n M) * M
      * Matrix.diagonal (rightWeylScale n (rowNormalize n M hrow)) :=
  sinkhornTwoStep_eq_weylGauge (n := n) M hrow hcol

/--
The phase RN barrier is the nonnegative scalar thermodynamic force/readout for
the corresponding finite Weyl-gauge Sinkhorn step.
-/
@[rep_depth transport, capstone]
theorem phaseRNBarrier_thermodynamicForce_nonneg
    (phase : SinkhornPhase)
    (M : SinkhornMatrix n) :
    0 ≤ phaseRNBarrierBefore n phase M :=
  phaseRNBarrierBefore_nonneg (n := n) phase M

/--
Admissible Sinkhorn transport decreases the phase-aligned RN force budget.
-/
@[rep_depth transport, capstone]
theorem sinkhornStep_RNForce_monotone
    {phase : SinkhornPhase}
    {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' ≤ phaseRNBarrierBefore n phase M :=
  sinkhornStep_phaseRNBarrier_monotone (n := n) hstep

/--
An admissible step gauge-fixes the corresponding post-step RN force to zero on
the normalized axis.
-/
@[rep_depth transport, capstone]
theorem sinkhornStep_postRNForce_eq_zero
    {phase : SinkhornPhase}
    {M M' : SinkhornMatrix n}
    (hstep : SinkhornStep n phase M M') :
    phaseRNBarrierAfter n phase M' = 0 :=
  sinkhornStep_phaseRNBarrierAfter_eq_zero (n := n) hstep

/--
The trajectory RN budget is monotone along the explicit Sinkhorn trajectory.
-/
@[rep_depth transport, capstone]
theorem trajectoryRNForce_monotone
    (T : SinkhornTrajectory n)
    (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ trajectoryRNBarrier n T k :=
  trajectoryRNBarrier_monotone (n := n) T k

end FiniteGaugeThermodynamics

section KMSBudget

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
KMS residual control is the operator-side consumer of the Sinkhorn RN gauge
budget.
-/
@[rep_depth transport]
theorem sinkhornGaugeBudget_controls_approxKMS
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hControl : SinkhornKMSControl n T K ω β) :
    SinkhornApproxKMSClosure n T K ω β := by
  intro k A B
  exact hControl k A B

/--
Zero RN gauge budget upgrades approximate KMS closure to exact KMS closure.
-/
@[rep_depth transport, capstone]
theorem sinkhornGaugeBudget_zero_forces_KMSClosure
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hApproxClosure : SinkhornApproxKMSClosure n T K ω β)
    (hBarrierZero : ∀ k : Nat, trajectoryRNBarrierNext n T k = 0) :
    SinkhornKMSClosure n T K ω β :=
  sinkhorn_step_kmsClosure_of_approxClosure_of_barrierZero
    (n := n) T K ω β hApproxClosure hBarrierZero

end KMSBudget

end InfoGeometry.Canonical.SinkhornGaugeThermodynamicsBridge

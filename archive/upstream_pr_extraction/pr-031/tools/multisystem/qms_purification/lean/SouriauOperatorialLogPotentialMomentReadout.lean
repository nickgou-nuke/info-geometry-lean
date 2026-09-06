import Mathlib

/-!
QMS isolated proof targets for purifying the `MomentGeneratingReadout` block in
`InfoGeometry.Canonical.SouriauOperatorialLogPotential`.

Mathematical context:
- `Param` is the parameter carrier.
- `Op` is the operator/observable carrier with multiplication.
- `OperatorialExponentialFamily Param Op` supplies a normalized state and scalar
  trace/readout.
- `MomentGeneratingReadout.firstMoment β O` is intended to be the traced first
  moment of observable `O` in the normalized state at `β`.
- `MomentGeneratingReadout.bkmCovariance β A B` is intended to be a symmetric
  positive-semidefinite BKM covariance form.
- `MomentGeneratingReadout.nResponseForm n β args` is intended to package the
  first and second response/cumulant readouts.

Existing mathlib/literature context:
- Mathlib has algebra/order primitives for equality, products, and nonnegativity,
  but this abstract owner surface does not define a concrete trace, Hilbert-space
  operator algebra, Kubo--Mori integral, or BKM inner product.
- In the operator-algebra literature, first-moment and BKM covariance laws require
  state/readout and positivity/symmetry hypotheses. Those are not derivable from
  arbitrary functions.

QMS purification move:
- Add precise proof-obligation fields for the four laws already claimed.
- Prove each public theorem as a field readback.
- Do not claim analytic BKM construction or positivity beyond the supplied field.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialMomentReadout

structure OperatorialExponentialFamily (Param Op : Type*) where
  K : Param → Op
  untracedExponential : Param → Op
  traceReadout : Op → ℝ
  partitionFunction : Param → ℝ
  partitionFunction_eq_trace : ∀ β, partitionFunction β = traceReadout (untracedExponential β)
  partitionPotential : Param → ℝ
  normalizedState : Param → Op
  partitionPotential_eq_log_trace : ∀ β, partitionPotential β = Real.log (partitionFunction β)

structure MomentGeneratingReadout (Param Op : Type*) [Mul Op] where
  family : OperatorialExponentialFamily Param Op
  firstMoment : Param → Op → ℝ
  bkmCovariance : Param → Op → Op → ℝ
  nResponseForm : Nat → Param → List Op → ℝ
  firstMoment_eq_trace_normalized_mul :
    ∀ β O, firstMoment β O = family.traceReadout (family.normalizedState β * O)
  bkmCovariance_symm :
    ∀ β A B, bkmCovariance β A B = bkmCovariance β B A
  bkmCovariance_self_nonneg :
    ∀ β A, 0 ≤ bkmCovariance β A A
  nResponseForm_one_two_eq :
    ∀ β A B,
      nResponseForm 1 β [A] = firstMoment β A ∧
      nResponseForm 2 β [A, B] = bkmCovariance β A B

/-- First moment readback from the supplied normalized trace law. -/
theorem firstMomentLaw_from_field
    {Param Op : Type*} [Mul Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (O : Op) :
    M.firstMoment β O = M.family.traceReadout (M.family.normalizedState β * O) := by
  exact M.firstMoment_eq_trace_normalized_mul β O

/-- BKM covariance symmetry readback from the supplied symmetry law. -/
theorem bkmCovarianceSymmetry_from_field
    {Param Op : Type*} [Mul Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (A B : Op) :
    M.bkmCovariance β A B = M.bkmCovariance β B A := by
  exact M.bkmCovariance_symm β A B

/-- BKM covariance nonnegativity readback from the supplied PSD law. -/
theorem bkmCovariancePSD_from_field
    {Param Op : Type*} [Mul Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (A : Op) :
    M.bkmCovariance β A A ≥ 0 := by
  exact M.bkmCovariance_self_nonneg β A

/-- Boundary readback identifying first and second response forms. -/
theorem higherCumulantBoundary_from_field
    {Param Op : Type*} [Mul Op]
    (M : MomentGeneratingReadout Param Op) (β : Param) (A B : Op) :
    M.nResponseForm 1 β [A] = M.firstMoment β A ∧
    M.nResponseForm 2 β [A, B] = M.bkmCovariance β A B := by
  exact M.nResponseForm_one_two_eq β A B

end InfoGeometry.QMS.SouriauOperatorialLogPotentialMomentReadout

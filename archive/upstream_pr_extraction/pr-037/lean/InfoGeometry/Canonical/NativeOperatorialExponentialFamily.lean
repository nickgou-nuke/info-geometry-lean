import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

/-!
# Native operatorial exponential families

This owner is the noncommutative replacement for record-only exponential
readouts.  The exponential is defined by Mathlib's `NormedSpace.exp`; it is
not supplied as an unrelated operator-valued field.  The only compatibility
input is the genuine additive/commuting law for the generator.

No trace-class, KMS, or infinite-dimensional implementability claim is made
here.  `traceReadout` is an explicit scalar readout and remains separate from
the operator algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.NativeOperatorialExponentialFamily

open scoped BigOperators

structure Family (Time Op : Type*)
    [AddMonoid Time]
    [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op] where
  /-- Noncommutative generator indexed by additive time/parameter. -/
  generator : Time → Op
  /-- Scalar readout kept external to the operator multiplication. -/
  traceReadout : Op → ℝ
  /-- Additivity of the generator. -/
  generator_add : ∀ s t, generator (s + t) = generator s + generator t
  /-- The generator values commute, so their exponentials compose. -/
  generator_commute : ∀ s t, Commute (generator s) (generator t)

namespace Family

variable {Time Op : Type*}
variable [AddMonoid Time]
variable [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]

local instance : NormedAlgebra ℚ Op :=
  NormedAlgebra.restrictScalars ℚ ℝ Op

/-- The actual untraced operatorial exponential `exp(-K_t)`. -/
noncomputable def untracedExponential
    (F : Family Time Op) (t : Time) : Op :=
  NormedSpace.exp (-(F.generator t))

/-- The partition readout of the actual operatorial exponential. -/
noncomputable def partitionFunction
    (F : Family Time Op) (t : Time) : ℝ :=
  F.traceReadout (F.untracedExponential t)

@[simp]
theorem untracedExponential_eq_exp_neg
    (F : Family Time Op) (t : Time) :
    F.untracedExponential t = NormedSpace.exp (-(F.generator t)) :=
  rfl

@[simp]
theorem untracedExponential_zero
    (F : Family Time Op) (hzero : F.generator 0 = 0) :
    F.untracedExponential 0 = 1 := by
  rw [untracedExponential_eq_exp_neg, hzero, neg_zero]
  exact NormedSpace.exp_zero

/-- Additive parameter evolution composes in the noncommutative operator ring. -/
theorem untracedExponential_add
    (F : Family Time Op) (s t : Time) :
    F.untracedExponential (s + t) =
      F.untracedExponential s * F.untracedExponential t := by
  change NormedSpace.exp (-(F.generator (s + t))) =
    NormedSpace.exp (-(F.generator s)) * NormedSpace.exp (-(F.generator t))
  rw [F.generator_add]
  have hcomm : Commute (-(F.generator s)) (-(F.generator t)) := by
    exact (F.generator_commute s t).neg_left.neg_right
  rw [neg_add, NormedSpace.exp_add_of_commute hcomm]

theorem partitionFunction_eq_readout
    (F : Family Time Op) (t : Time) :
    F.partitionFunction t = F.traceReadout (F.untracedExponential t) :=
  rfl

end Family

end InfoGeometry.Canonical.NativeOperatorialExponentialFamily

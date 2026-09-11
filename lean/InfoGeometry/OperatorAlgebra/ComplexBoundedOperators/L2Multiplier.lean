import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.ENNReal.Holder
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Count

/-!
# CBO-013: complex `L²` multiplication operators

This file records the adapter-first Lean form of the AFP complex bounded
operator correspondence for multiplication operators.

The canonical operator is `mulOp`: multiplication by a fixed `L∞(μ)` function
as a bounded operator on complex-valued `L²(μ)`.

The discrete/counting-measure specialization is `discreteMulOp`.
-/

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace L2Multiplier

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Complex-valued `L²(μ)`. -/
abbrev L2c (α : Type*) [MeasurableSpace α] (μ : Measure α) : Type _ :=
  MeasureTheory.Lp ℂ (2 : ℝ≥0∞) μ

/-- Complex-valued `L∞(μ)`. -/
abbrev Linftyc (α : Type*) [MeasurableSpace α] (μ : Measure α) : Type _ :=
  MeasureTheory.Lp ℂ (∞ : ℝ≥0∞) μ

/-- Diagnostic: Lean resolves the Hölder triple `L∞ × L² → L²`. -/
example :
    ENNReal.HolderTriple
      (∞ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := by
  infer_instance

/--
CBO-013b: multiplication by a fixed `L∞(μ)` function as a bounded
linear operator on complex-valued `L²(μ)`.
-/
def mulOp (a : Linftyc α μ) : L2c α μ →L[ℂ] L2c α μ :=
  ({
    toFun := fun f => a • f
    map_add' := by
      intro f g
      exact MeasureTheory.Lp.add_smul a f g
    map_smul' := by
      intro c f
      simpa using
        (MeasureTheory.Lp.smul_comm (c := c) (f := a) (g := f)).symm
  } : L2c α μ →ₗ[ℂ] L2c α μ).mkContinuous ‖a‖ (by
    intro f
    exact MeasureTheory.Lp.norm_smul_le a f)

@[simp]
theorem mulOp_apply (a : Linftyc α μ) (f : L2c α μ) :
    mulOp (α := α) (μ := μ) a f = a • f := by
  rfl

/-- The operator is pointwise multiplication, modulo a.e. equality. -/
theorem mulOp_apply_ae (a : Linftyc α μ) (f : L2c α μ) :
    ⇑(mulOp (α := α) (μ := μ) a f) =ᵐ[μ] fun x => a x * f x := by
  simpa [mulOp_apply, smul_eq_mul] using
    (MeasureTheory.Lp.coeFn_lpSMul a f)

/-- Pointwise operator norm estimate. -/
theorem norm_mulOp_apply_le (a : Linftyc α μ) (f : L2c α μ) :
    ‖mulOp (α := α) (μ := μ) a f‖ ≤ ‖a‖ * ‖f‖ := by
  simpa [mulOp_apply] using
    (MeasureTheory.Lp.norm_smul_le a f)

/-- Operator norm estimate: `‖M_a‖ ≤ ‖a‖∞`. -/
theorem norm_mulOp_le (a : Linftyc α μ) :
    ‖mulOp (α := α) (μ := μ) a‖ ≤ ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) ?_
  intro f
  exact norm_mulOp_apply_le a f

/--
Conceptual bilinear version:
`L∞(μ) →L[ℂ] L²(μ) →L[ℂ] L²(μ)`.

This is not the canonical downstream definition, because `mulOp` unfolds
directly to `a • f`; this version records the Hölder/continuous-bilinear-map
origin.
-/
def mulOpBilinear :
    Linftyc α μ →L[ℂ] L2c α μ →L[ℂ] L2c α μ :=
  ContinuousLinearMap.holderL μ
    (∞ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞)
    (ContinuousLinearMap.mul ℂ ℂ)

section Discrete

variable {ι : Type*} [MeasurableSpace ι]

/--
Counting-measure `ℓ²` model.

For the closest raw sequence-space correspondence, the surrounding bridge can
instantiate a genuinely discrete/countable measurable space. The proofs below
need only `[MeasurableSpace ι]`.
-/
abbrev ell2Count (ι : Type*) [MeasurableSpace ι] : Type _ :=
  L2c ι (Measure.count : Measure ι)

/-- Counting-measure `ℓ∞` model. -/
abbrev ellInfCount (ι : Type*) [MeasurableSpace ι] : Type _ :=
  Linftyc ι (Measure.count : Measure ι)

/--
CBO-013a: discrete/counting-measure multiplication operator.

This is deliberately named differently from `mulOp` to avoid namespace noise
in larger adapter files.
-/
def discreteMulOp (a : ellInfCount ι) :
    ell2Count ι →L[ℂ] ell2Count ι :=
  mulOp (α := ι) (μ := (Measure.count : Measure ι)) a

@[simp]
theorem discreteMulOp_apply (a : ellInfCount ι) (f : ell2Count ι) :
    discreteMulOp (ι := ι) a f = a • f := by
  rfl

/--
For counting measure, a.e. equality becomes pointwise equality, so the discrete
operator satisfies the expected sequence formula.
-/
theorem discreteMulOp_apply_pointwise (a : ellInfCount ι) (f : ell2Count ι) :
    ∀ i : ι, (discreteMulOp (ι := ι) a f) i = a i * f i := by
  have h :=
    MeasureTheory.Measure.ae_count_iff.mp
      (mulOp_apply_ae
        (α := ι) (μ := (Measure.count : Measure ι)) a f)
  simpa [discreteMulOp] using h

/-- Discrete pointwise operator norm estimate. -/
theorem norm_discreteMulOp_apply_le (a : ellInfCount ι) (f : ell2Count ι) :
    ‖discreteMulOp (ι := ι) a f‖ ≤ ‖a‖ * ‖f‖ := by
  simpa [discreteMulOp] using
    (norm_mulOp_apply_le
      (α := ι) (μ := (Measure.count : Measure ι)) a f)

/-- Discrete operator norm estimate: `‖M_a‖ ≤ ‖a‖∞`. -/
theorem norm_discreteMulOp_le (a : ellInfCount ι) :
    ‖discreteMulOp (ι := ι) a‖ ≤ ‖a‖ := by
  simpa [discreteMulOp] using
    (norm_mulOp_le
      (α := ι) (μ := (Measure.count : Measure ι)) a)

end Discrete

end L2Multiplier
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

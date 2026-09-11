import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.L2Multiplier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# AFP `ket` semantics for counting-measure `ell2Count`

This file exposes the first `Complex_L2` adapter layer from AFP:

* AFP carrier: `'a ell2`;
* Lean carrier: `Lp ℂ 2 Measure.count`, already named `L2Multiplier.ell2Count`;
* AFP basis vector: `ket i`;
* Lean basis vector: the `L²(count)` class of the singleton indicator `{i}`.

This is a semantic Lean implementation, not proof-object transport.
-/

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace L2Multiplier

section Ket

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- AFP `ket i`: the singleton indicator basis vector in counting-measure `L²`. -/
def ket (i : ι) : ell2Count ι :=
  MeasureTheory.indicatorConstLp
    (μ := (Measure.count : Measure ι))
    (2 : ℝ≥0∞)
    (measurableSet_singleton i)
    (by simp [MeasureTheory.Measure.count_singleton i])
    (1 : ℂ)

/-- The a.e. representative of `ket i` is the singleton indicator of `{i}`. -/
theorem ket_apply_ae (i : ι) :
    ⇑(ket i) =ᵐ[(Measure.count : Measure ι)]
      ({i} : Set ι).indicator (fun _ => (1 : ℂ)) := by
  dsimp [ket]
  exact MeasureTheory.indicatorConstLp_coeFn

/-- For counting measure, `ket i` has the expected pointwise singleton value. -/
theorem ket_apply_pointwise (i j : ι) :
    ket i j = ({i} : Set ι).indicator (fun _ => (1 : ℂ)) j := by
  exact MeasureTheory.Measure.ae_count_iff.mp (ket_apply_ae i) j

@[simp]
theorem ket_apply_self (i : ι) :
    ket i i = 1 := by
  simpa using ket_apply_pointwise (ι := ι) i i

theorem ket_apply_of_ne {i j : ι} (hij : j ≠ i) :
    ket i j = 0 := by
  simpa [Set.indicator, hij] using ket_apply_pointwise (ι := ι) i j

/-- AFP `norm_ket`: singleton indicator basis vectors have norm one. -/
@[simp]
theorem norm_ket (i : ι) :
    ‖ket i‖ = 1 := by
  rw [ket, MeasureTheory.norm_indicatorConstLp]
  simp [MeasureTheory.count_real_singleton]
  · norm_num
  · norm_num

/-- AFP `ket_injective`: different indices give different singleton basis vectors. -/
@[simp]
theorem ket_injective {i j : ι} :
    ket i = ket j ↔ i = j := by
  constructor
  · intro hij
    by_contra hne
    have hcoord : ket i i = ket j i := congrArg (fun f : ell2Count ι => f i) hij
    rw [ket_apply_self, ket_apply_of_ne hne] at hcoord
    exact one_ne_zero hcoord
  · intro hij
    rw [hij]

/-- Function-level injectivity form of `ket_injective`. -/
theorem inj_ket :
    Function.Injective (ket : ι → ell2Count ι) := by
  intro i j h
  exact ket_injective.mp h

end Ket

end L2Multiplier
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators


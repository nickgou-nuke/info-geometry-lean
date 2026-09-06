import InfoGeometry.OperatorAlgebra.FiniteParityHomotopySupertrace
import InfoGeometry.LinearAlgebra.TraceKernelRangeTransport

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

namespace TwoPeriodicComplex

open InfoGeometry.LinearAlgebra

variable {Vplus Vminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]

namespace Hom

variable {C : TwoPeriodicComplex Vplus Vminus}

theorem positiveCarrierTrace_eq_cycle_add_range
    (f : Hom C C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    LinearMap.trace ℝ Vplus f.positive =
      LinearMap.trace ℝ (LinearMap.ker C.dPlus) f.positiveCycleMap +
        LinearMap.trace ℝ (LinearMap.range C.dPlus)
          (TraceKernelRangeTransport.rangeRestriction
            C.dPlus f.positive f.negative f.commutes_dPlus) := by
  calc
    LinearMap.trace ℝ Vplus f.positive =
        LinearMap.trace ℝ (LinearMap.ker C.dPlus) f.positiveCycleMap +
          LinearMap.trace ℝ (Vplus ⧸ LinearMap.ker C.dPlus)
            (TraceKernelRangeTransport.quotientByKernelMap
              C.dPlus f.positive f.negative f.commutes_dPlus) := by
      simpa [TraceInvariantSubmodule.invariantRestriction,
        TraceInvariantSubmodule.invariantQuotientMap,
        TraceKernelRangeTransport.quotientByKernelMap,
        positiveCycleMap] using
        (TraceInvariantSubmodule.trace_eq_trace_restriction_add_trace_quotient
          f.positive (LinearMap.ker C.dPlus)
          (TraceKernelRangeTransport.kernel_invariant
            C.dPlus f.positive f.negative f.commutes_dPlus))
    _ = _ := by
      rw [TraceKernelRangeTransport.trace_quotientByKernel_eq_trace_rangeRestriction
        C.dPlus f.positive f.negative f.commutes_dPlus]

theorem negativeCarrierTrace_eq_cycle_add_range
    (f : Hom C C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    LinearMap.trace ℝ Vminus f.negative =
      LinearMap.trace ℝ (LinearMap.ker C.dMinus) f.negativeCycleMap +
        LinearMap.trace ℝ (LinearMap.range C.dMinus)
          (TraceKernelRangeTransport.rangeRestriction
            C.dMinus f.negative f.positive f.commutes_dMinus) := by
  calc
    LinearMap.trace ℝ Vminus f.negative =
        LinearMap.trace ℝ (LinearMap.ker C.dMinus) f.negativeCycleMap +
          LinearMap.trace ℝ (Vminus ⧸ LinearMap.ker C.dMinus)
            (TraceKernelRangeTransport.quotientByKernelMap
              C.dMinus f.negative f.positive f.commutes_dMinus) := by
      simpa [TraceInvariantSubmodule.invariantRestriction,
        TraceInvariantSubmodule.invariantQuotientMap,
        TraceKernelRangeTransport.quotientByKernelMap,
        negativeCycleMap] using
        (TraceInvariantSubmodule.trace_eq_trace_restriction_add_trace_quotient
          f.negative (LinearMap.ker C.dMinus)
          (TraceKernelRangeTransport.kernel_invariant
            C.dMinus f.negative f.positive f.commutes_dMinus))
    _ = _ := by
      rw [TraceKernelRangeTransport.trace_quotientByKernel_eq_trace_rangeRestriction
        C.dMinus f.negative f.positive f.commutes_dMinus]

theorem positiveCycleTrace_eq_boundary_add_cohomology
    (f : Hom C C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    LinearMap.trace ℝ (LinearMap.ker C.dPlus) f.positiveCycleMap =
      LinearMap.trace ℝ C.positiveBoundaries
          (TraceInvariantSubmodule.invariantRestriction
            f.positiveCycleMap C.positiveBoundaries
            f.maps_positiveBoundaries) +
        LinearMap.trace ℝ C.PositiveCohomology
          f.positiveCohomologyMap := by
  simpa [TraceInvariantSubmodule.invariantQuotientMap,
    positiveCohomologyMap] using
    (TraceInvariantSubmodule.trace_eq_trace_restriction_add_trace_quotient
      f.positiveCycleMap C.positiveBoundaries f.maps_positiveBoundaries)

theorem negativeCycleTrace_eq_boundary_add_cohomology
    (f : Hom C C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    LinearMap.trace ℝ (LinearMap.ker C.dMinus) f.negativeCycleMap =
      LinearMap.trace ℝ C.negativeBoundaries
          (TraceInvariantSubmodule.invariantRestriction
            f.negativeCycleMap C.negativeBoundaries
            f.maps_negativeBoundaries) +
        LinearMap.trace ℝ C.NegativeCohomology
          f.negativeCohomologyMap := by
  simpa [TraceInvariantSubmodule.invariantQuotientMap,
    negativeCohomologyMap] using
    (TraceInvariantSubmodule.trace_eq_trace_restriction_add_trace_quotient
      f.negativeCycleMap C.negativeBoundaries f.maps_negativeBoundaries)

theorem positiveBoundaryTrace_eq_range
    (f : Hom C C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    LinearMap.trace ℝ C.positiveBoundaries
        (TraceInvariantSubmodule.invariantRestriction
          f.positiveCycleMap C.positiveBoundaries
          f.maps_positiveBoundaries) =
      LinearMap.trace ℝ (LinearMap.range C.dMinus)
        (TraceKernelRangeTransport.rangeRestriction
          C.dMinus f.negative f.positive f.commutes_dMinus) := by
  let T : Module.End ℝ C.positiveBoundaries :=
    TraceInvariantSubmodule.invariantRestriction
      f.positiveCycleMap C.positiveBoundaries f.maps_positiveBoundaries
  have hconj :
      C.positiveBoundaryEquivRange.conj T =
        TraceKernelRangeTransport.rangeRestriction
          C.dMinus f.negative f.positive f.commutes_dMinus := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  rw [← hconj]
  exact (LinearMap.trace_conj' T C.positiveBoundaryEquivRange).symm

theorem negativeBoundaryTrace_eq_range
    (f : Hom C C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    LinearMap.trace ℝ C.negativeBoundaries
        (TraceInvariantSubmodule.invariantRestriction
          f.negativeCycleMap C.negativeBoundaries
          f.maps_negativeBoundaries) =
      LinearMap.trace ℝ (LinearMap.range C.dPlus)
        (TraceKernelRangeTransport.rangeRestriction
          C.dPlus f.positive f.negative f.commutes_dPlus) := by
  let T : Module.End ℝ C.negativeBoundaries :=
    TraceInvariantSubmodule.invariantRestriction
      f.negativeCycleMap C.negativeBoundaries f.maps_negativeBoundaries
  have hconj :
      C.negativeBoundaryEquivRange.conj T =
        TraceKernelRangeTransport.rangeRestriction
          C.dPlus f.positive f.negative f.commutes_dPlus := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  rw [← hconj]
  exact (LinearMap.trace_conj' T C.negativeBoundaryEquivRange).symm

theorem hopfTrace
    (f : Hom C C)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    f.carrierSupertrace = f.cohomologySupertrace := by
  rw [carrierSupertrace, cohomologySupertrace,
    positiveCarrierTrace_eq_cycle_add_range,
    negativeCarrierTrace_eq_cycle_add_range,
    positiveCycleTrace_eq_boundary_add_cohomology,
    negativeCycleTrace_eq_boundary_add_cohomology,
    positiveBoundaryTrace_eq_range,
    negativeBoundaryTrace_eq_range]
  ring

end Hom

end TwoPeriodicComplex

end InfoGeometry.OperatorAlgebra.FiniteParityComplex

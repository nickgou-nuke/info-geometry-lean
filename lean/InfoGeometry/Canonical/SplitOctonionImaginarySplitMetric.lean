import InfoGeometry.Algebra.SplitMetricSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionImaginaryEllSupport

/-!
# Native split metric packaging for the imaginary split-octonions

The metric is the existing determinant-polar form.  This file only packages
it in the shared `SplitMetricSpace` interface and records the already proved
skew-adjoint operator `imaginaryEllT` in Mathlib's native Lie subalgebra.
-/

namespace InfoGeometry.Lie.SplitOctonionImaginaryEllSupport

open InfoGeometry.Algebra
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor

noncomputable def imaginarySplitMetric : SplitMetricSpace ℝ where
  V := Imaginary
  beta := imaginaryPolarBilin
  beta_symm := imaginaryPolarBilin_isSymm
  beta_nondegenerate := by
    constructor
    · intro X h
      apply imaginaryPolarBilin_nondegenerate X
      intro Y
      exact h Y
    · intro Y h
      apply imaginaryPolarBilin_nondegenerate Y
      intro X
      rw [imaginaryPolarBilin_isSymm.eq]
      exact h X

theorem imaginaryEllT_mem_imaginarySplitMetric_skew :
    SplitOctonionImaginaryEllPolarization.imaginaryEllT ∈
      LinearMap.skewAdjointSubmodule imaginaryPolarBilin := by
  change (-imaginaryPolarBilin).IsPairSelfAdjoint imaginaryPolarBilin
    SplitOctonionImaginaryEllPolarization.imaginaryEllT
  intro X Y
  change imaginaryPolarBilin
      (SplitOctonionImaginaryEllPolarization.imaginaryEllT X) Y =
    -imaginaryPolarBilin X
      (SplitOctonionImaginaryEllPolarization.imaginaryEllT Y)
  exact imaginaryEllT_skew_adjoint X Y

end InfoGeometry.Lie.SplitOctonionImaginaryEllSupport

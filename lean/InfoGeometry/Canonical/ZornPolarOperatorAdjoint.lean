/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornPolarAdjoint
import InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! Native regular operators and their uniquely determined split-polar adjoints.
No positive-definiteness of the split form is asserted. -/
namespace InfoGeometry.Canonical.ZornPolarOperatorAdjoint
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarAdjoint
open ZornRealRegularMultiplicationSpectralBridge

theorem polarForm_nondegenerate : polarForm.Nondegenerate := by
  constructor
  · intro X h
    exact (hilbertized_zero_iff X).mp (h (fundamental X))
  · intro X h
    apply (hilbertized_zero_iff X).mp
    rw [polarPair_symm]
    exact h (fundamental X)

theorem leftRegular_adjoint (X : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm
      (leftRegular X) (leftRegular (zornConj X)) :=
  polar_left_adjoint X

theorem rightRegular_adjoint (X : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm
      (rightRegular X) (rightRegular (zornConj X)) :=
  polar_right_adjoint X

/-- Nondegeneracy makes the operator satisfying this adjunction unique. -/
theorem polar_adjoint_unique (T S U : Module.End ℝ ZornCoord)
    (hS : LinearMap.IsAdjointPair polarForm polarForm T S)
    (hU : LinearMap.IsAdjointPair polarForm polarForm T U) : S = U := by
  apply LinearMap.ext
  intro Y
  apply sub_eq_zero.mp
  apply polarForm_nondegenerate.2
  intro X
  rw [map_sub, ← hS X Y, ← hU X Y, sub_self]

end InfoGeometry.Canonical.ZornPolarOperatorAdjoint

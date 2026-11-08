/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ISBarrierDerivativeBridge

#print axioms InfoGeometry.Canonical.SelfConcordantZetaBarrier.hasDerivAt_isBarrierKernel
#print axioms InfoGeometry.Canonical.SelfConcordantZetaBarrier.hasDerivAt_isBarrierKernel_deriv
#print axioms InfoGeometry.Canonical.SelfConcordantZetaBarrier.hasDerivAt_isBarrierKernel_deriv2
#print axioms InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov.hasDerivAt_potential_along_field
#print axioms InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov.deriv_potential_along_field_nonpos
#print axioms InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov.deriv_potential_along_field_neg

open InfoGeometry.Canonical.SelfConcordantZetaBarrier
open InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

example : HasDerivAt isBarrierKernel (1 / 2) 2 := by
  convert hasDerivAt_isBarrierKernel (x := 2) (by norm_num) using 1
  norm_num [isBarrierKernel_deriv]

/-- The trajectory hypothesis has a concrete stationary inhabitant for every rate. -/
example (κ t : ℝ) :
    HasDerivAt (fun _ : ℝ => lyapunovPotential 1) 0 t := by
  have hγ : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (naturalGradientField κ 1) t := by
    simpa [naturalGradientField, isBarrierKernel_deriv] using hasDerivAt_const t (1 : ℝ)
  simpa using hasDerivAt_potential_along_field (by norm_num) hγ

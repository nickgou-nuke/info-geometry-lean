/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.ThreeProbeReconstruction

namespace InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

example : nonSeparatingMatrix = invisibleRows (fun _ => 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [nonSeparatingMatrix, invisibleRows]

example : ∃! c, nonSeparatingMatrix = invisibleRows c := by
  apply (two_probe_kernel_unique _).mp
  exact ⟨two_probes_do_not_separate.1, two_probes_do_not_separate.2.1⟩

example : reconstructProbes (nonSeparatingMatrix.mulVec probeP1)
    (nonSeparatingMatrix.mulVec probeP2) (nonSeparatingMatrix.mulVec probeP3) =
      nonSeparatingMatrix := reconstructProbes_readback _

#print axioms invisibleRows_injective
#print axioms two_probe_kernel_iff
#print axioms two_probe_kernel_unique
#print axioms two_probe_fiber_iff
#print axioms reconstructProbes_readback
#print axioms three_probes_injective
#print axioms two_probes_do_not_separate

end InfoGeometry.Synthesis.SedenionSocleDirectSumSeparationBridge

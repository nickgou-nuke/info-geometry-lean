/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.POM.FiberSpectrumFiniteReconstructionSharp

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-spectrum-two-atom-complete-invariant`. The threshold window
specializes to `4` at two atoms, and the concrete moment Hankel matrix has rank `2`. This module
does not prove complete-invariant reconstruction from a moment prefix. -/
theorem paper_pom_fiber_spectrum_two_atom_complete_invariant
    (D : FiberSpectrumPronyHankelRankData) (h2 : D.atomCount = 2) :
    pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount = 4 ∧
      pom_fiber_spectrum_finite_reconstruction_sharp_rank D := by
  rcases paper_pom_fiber_spectrum_finite_reconstruction_sharp D (by simp [h2]) with
    ⟨hwindow, hreconstruct, _, _⟩
  refine ⟨?_, hreconstruct⟩
  calc
    pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount = 2 * D.atomCount := hwindow
    _ = 4 := by simp [h2]

end Omega.POM

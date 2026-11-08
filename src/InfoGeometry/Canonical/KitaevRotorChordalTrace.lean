/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryTraceNormalization
import InfoGeometry.Canonical.KitaevRotorMatrix
import InfoGeometry.Canonical.PeirceRotorChordal

/-! Chordal trace identities on the actual two-site chain operator carrier.
The full-support multiplicity differs from the proper-support Zorn null pair.
These are ordinary traces of algebraic squares, not Dirac-adjoint norms. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevRotorChordalTrace
open KitaevConcreteBoundary KitaevBoundaryDiracPair KitaevBoundaryTraceNormalization
open KitaevRotorMatrix PeirceRotorAction PeirceRotorChordal

theorem twoSite_moving_trace (c s : ℂ) :
    Matrix.trace (movingPlus c s (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators)) = 2*(c*c+s*s) := by
  rw [boundary_movingPlus_eq_matrix, boundaryMatrixHom_trace]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem twoSite_displacement_trace (c s : ℂ) (hc : c*c+s*s=1) :
    let d := boundaryAnnihilation (by decide) twoSiteOperators
    let B := boundaryCreation (by decide) twoSiteOperators
    Matrix.trace ((movingPlus c s d B-d*B)*(movingPlus c s d B-d*B)) = 4*(s*s) := by
  dsimp only
  rw [movingPlus_displacement_square (boundaryAnnihilation_sq (by decide) twoSiteOperators)
    (boundaryCreation_sq (by decide) twoSiteOperators)
    (boundary_reflexive (by decide) twoSiteOperators).1
    (boundary_reflexive (by decide) twoSiteOperators).2 c s hc, boundary_support,
    Matrix.trace_smul, Matrix.trace_one]
  norm_num
  ring

end InfoGeometry.Canonical.KitaevRotorChordalTrace

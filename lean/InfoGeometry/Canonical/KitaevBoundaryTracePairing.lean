/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevConcreteBoundary
import InfoGeometry.Canonical.KitaevBoundaryPeirce
import InfoGeometry.CliffordWeyl.DiracPeircePairing

/-! Nondegeneracy of the actual two-site boundary Peirce trace pairing with
its constructed Dirac adjoint. No positive-definite inner product is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryTracePairing
open CARMajoranaFiniteBridge KitaevConcreteBoundary KitaevBoundaryDiracPair
open InfoGeometry.Core.PeirceDecomposition

abbrev boundaryOccupation : ChainOp :=
  boundaryAnnihilation (by decide) twoSiteOperators *
    boundaryCreation (by decide) twoSiteOperators

theorem boundaryOccupation_dirac_fixed :
    twoSiteKreinData.diracAdjoint boundaryOccupation = boundaryOccupation :=
  KitaevBoundaryPeirce.boundary_product_dirac_fixed (by decide) twoSiteOperators
    (twoSite_star 0) (twoSite_star 3)

/-- Testing against all Dirac-conjugated boundary corners detects zero. -/
theorem component10_trace_separates (X : ChainOp)
    (hX : component10 boundaryOccupation X = X)
    (h : ∀ Y, Matrix.trace
      (X * twoSiteKreinData.diracAdjoint (component10 boundaryOccupation Y)) = 0) : X = 0 :=
  twoSiteKreinData.component10_eq_zero_of_dirac_trace_pairing boundaryOccupation X
    boundaryOccupation_dirac_fixed hX h

theorem component01_trace_separates (X : ChainOp)
    (hX : component01 boundaryOccupation X = X)
    (h : ∀ Y, Matrix.trace
      (X * twoSiteKreinData.diracAdjoint (component01 boundaryOccupation Y)) = 0) : X = 0 :=
  twoSiteKreinData.component01_eq_zero_of_dirac_trace_pairing boundaryOccupation X
    boundaryOccupation_dirac_fixed hX h

end InfoGeometry.Canonical.KitaevBoundaryTracePairing

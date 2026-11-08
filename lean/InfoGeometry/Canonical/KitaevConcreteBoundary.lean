/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARMajoranaMatrices
import InfoGeometry.Canonical.KitaevBoundaryKrein
import InfoGeometry.Canonical.KitaevBoundaryConstructedMetric

/-! The native chain interface instantiated by the existing full two-site
Jordan–Wigner matrices. No assumed Clifford or star laws remain. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevConcreteBoundary
open CARMajoranaFiniteBridge InfoGeometry.Quantum.KitaevChain

theorem twoSite_square (i : Fin 4) : twoSiteMajorana i * twoSiteMajorana i = 1 := by
  apply smul_right_injective (M := ChainOp) (by norm_num : (2 : ℂ) ≠ 0)
  simpa [two_smul, show (2 : ChainOp) = 1 + 1 by norm_num] using
    twoSiteMajorana_car i i

/-- Concrete full-matrix Clifford family for the native finite chain. -/
def twoSiteOperators : MajoranaCliffordOperators 2 ChainOp where
  γ := twoSiteMajorana
  h_ortho i j hij := by simpa [hij] using twoSiteMajorana_car i j
  h_sq := twoSite_square

theorem twoSite_star (i : Fin 4) : star (twoSiteOperators.γ i) = twoSiteOperators.γ i :=
  twoSiteMajorana_selfAdjoint i

open KitaevBoundaryDiracPair KitaevBoundaryConstructedMetric KitaevBoundaryKrein

/-- An actual metric-adjoint datum from the two concrete boundary matrices. -/
def twoSiteKreinData : InfoGeometry.Physics.KasparovKreinData ChainOp :=
  endpointKreinData (by decide : 0 < 2) twoSiteOperators (twoSite_star 0) (twoSite_star 3)

theorem twoSite_boundary_dirac :
    twoSiteKreinData.diracAdjoint (boundaryAnnihilation (by decide) twoSiteOperators) =
      -boundaryCreation (by decide) twoSiteOperators :=
  boundaryAnnihilation_dirac_of_negative (by decide) twoSiteOperators twoSiteKreinData
    (endpointKreinData_left_negative _ _ _ _) (endpointKreinData_right_negative _ _ _ _)

/-- Full represented matrix compatibility, with no assumed metric-sign hypotheses. -/
theorem twoSite_pairMatrix_dirac (M : Matrix (Fin 2) (Fin 2) ℂ) :
    twoSiteKreinData.diracAdjoint
      (ReflexiveNilpotentFlows.pairMatrixLinear
        (boundaryAnnihilation (by decide) twoSiteOperators)
        (boundaryCreation (by decide) twoSiteOperators) M) =
      ReflexiveNilpotentFlows.pairMatrixLinear
        (boundaryAnnihilation (by decide) twoSiteOperators)
        (boundaryCreation (by decide) twoSiteOperators)
        (ReflexiveNilpotentFlows.pairDiracMetric * M.conjTranspose *
          ReflexiveNilpotentFlows.pairDiracMetric) :=
  boundary_pairMatrix_dirac (by decide) twoSiteOperators twoSiteKreinData
    (endpointKreinData_left_negative _ _ _ _) (endpointKreinData_right_negative _ _ _ _) M

end InfoGeometry.Canonical.KitaevConcreteBoundary

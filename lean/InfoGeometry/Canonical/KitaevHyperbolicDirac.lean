/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceHyperbolicComposition
import InfoGeometry.Canonical.KitaevBoundaryFaithful
import InfoGeometry.Canonical.KitaevConcreteBoundary

/-! Native hyperbolic boosts preserve the constructed Dirac metric for
star-fixed parameters. This does not assert ordinary Hilbert unitarity. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevHyperbolicDirac
open CARMajoranaFiniteBridge KitaevConcreteBoundary KitaevBoundaryDiracPair
open KitaevBoundaryAlgebra KitaevBoundaryFaithful ReflexiveNilpotentFlows
open PeirceMatrixUnitCompletion PeirceHyperbolicOrbit

def twoSiteBoost (u v : ℂ) (h : u*u-v*v=1) : ChainOpˣ :=
  hyperbolicUnit (boundaryAnnihilation_sq (by decide) twoSiteOperators)
    (boundaryCreation_sq (by decide) twoSiteOperators)
    (boundary_reflexive (by decide) twoSiteOperators).1
    (boundary_reflexive (by decide) twoSiteOperators).2 u v h

theorem twoSiteBoost_matrix (u v : ℂ) (h : u*u-v*v=1) :
    (twoSiteBoost u v h : ChainOp) =
      boundaryMatrixHom (by decide) twoSiteOperators !![u, v; v, u] := by
  change completedMatrix _ _ _ = _
  unfold completedMatrix complement
  rw [boundary_support, sub_self, zero_add]
  rfl

theorem twoSiteBoost_inverse_matrix (u v : ℂ) (h : u*u-v*v=1) :
    (↑(twoSiteBoost u v h)⁻¹ : ChainOp) =
      boundaryMatrixHom (by decide) twoSiteOperators !![u, -v; -v, u] := by
  change completedMatrix _ _ _ = _
  unfold completedMatrix complement
  rw [boundary_support, sub_self, zero_add]
  rfl

theorem twoSiteBoost_dirac_inverse (u v : ℂ) (h : u*u-v*v=1)
    (hu : star u=u) (hv : star v=v) :
    twoSiteKreinData.diracAdjoint (twoSiteBoost u v h : ChainOp) =
      (↑(twoSiteBoost u v h)⁻¹ : ChainOp) := by
  rw [twoSiteBoost_matrix, twoSiteBoost_inverse_matrix]
  unfold twoSiteKreinData
  rw [boundaryMatrixHom_dirac (by decide) twoSiteOperators (twoSite_star 0) (twoSite_star 3)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairDiracMetric, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two,
      (show (starRingEnd ℂ) u = u from hu), (show (starRingEnd ℂ) v = v from hv)]

theorem hyperbolicPlus_dirac_fixed (u v : ℂ) (hu : star u=u) (hv : star v=v) :
    twoSiteKreinData.diracAdjoint
      (hyperbolicPlus u v (boundaryAnnihilation (by decide) twoSiteOperators)
        (boundaryCreation (by decide) twoSiteOperators)) =
      hyperbolicPlus u v (boundaryAnnihilation (by decide) twoSiteOperators)
        (boundaryCreation (by decide) twoSiteOperators) := by
  change twoSiteKreinData.diracAdjoint
    (boundaryMatrixHom (by decide) twoSiteOperators (hyperbolicMatrix u v)) =
      boundaryMatrixHom (by decide) twoSiteOperators (hyperbolicMatrix u v)
  unfold twoSiteKreinData
  rw [boundaryMatrixHom_dirac (by decide) twoSiteOperators (twoSite_star 0) (twoSite_star 3)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMatrix, pairDiracMetric, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two,
      (show (starRingEnd ℂ) u = u from hu), (show (starRingEnd ℂ) v = v from hv)]

end InfoGeometry.Canonical.KitaevHyperbolicDirac

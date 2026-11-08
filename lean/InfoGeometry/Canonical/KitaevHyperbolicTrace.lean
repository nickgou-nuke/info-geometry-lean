/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevHyperbolicDirac
import InfoGeometry.Canonical.KitaevBoundaryTraceNormalization

/-! Hyperbolic displacement and its Dirac trace pairing on the native two-site
chain. The negative value uses the constructed indefinite adjoint, not a
positive Hilbert norm. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevHyperbolicTrace
open KitaevConcreteBoundary KitaevBoundaryDiracPair KitaevBoundaryAlgebra
open KitaevBoundaryTraceNormalization KitaevBoundaryTracePairing
open KitaevHyperbolicDirac PeirceHyperbolicOrbit

theorem hyperbolic_trace (u v : ℂ) :
    Matrix.trace (hyperbolicPlus u v
      (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators)) = 2*(u*u-v*v) := by
  change Matrix.trace (boundaryMatrixHom (by decide) twoSiteOperators
    (hyperbolicMatrix u v)) = _
  rw [boundaryMatrixHom_trace]
  simp [hyperbolicMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two, sub_eq_add_neg]

theorem displacement_square_trace (u v : ℂ) (h : u*u-v*v=1) :
    let H := hyperbolicPlus u v (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators)
    Matrix.trace ((H-boundaryOccupation)*(H-boundaryOccupation)) = -4*(v*v) := by
  dsimp only
  rw [hyperbolicPlus_displacement (boundaryAnnihilation_sq (by decide) twoSiteOperators)
    (boundaryCreation_sq (by decide) twoSiteOperators)
    (boundary_reflexive (by decide) twoSiteOperators).1
    (boundary_reflexive (by decide) twoSiteOperators).2 u v h,
    boundary_support, Matrix.trace_smul, Matrix.trace_one]
  norm_num
  ring

theorem displacement_dirac_trace (u v : ℂ) (h : u*u-v*v=1)
    (hu : star u=u) (hv : star v=v) :
    let H := hyperbolicPlus u v (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators)
    Matrix.trace ((H-boundaryOccupation)*
      twoSiteKreinData.diracAdjoint (H-boundaryOccupation)) = -4*(v*v) := by
  dsimp only
  have hsub (X Y : CARMajoranaFiniteBridge.ChainOp) :
      twoSiteKreinData.diracAdjoint (X-Y) =
        twoSiteKreinData.diracAdjoint X-twoSiteKreinData.diracAdjoint Y := by
    simp only [InfoGeometry.Physics.KasparovKreinData.diracAdjoint,
      star_sub, mul_sub, sub_mul]
  rw [hsub, hyperbolicPlus_dirac_fixed u v hu hv, boundaryOccupation_dirac_fixed]
  exact displacement_square_trace u v h

/-- A normalized nonzero boost with strictly negative Dirac trace pairing. -/
theorem rational_boost_displacement_trace :
    let H := hyperbolicPlus (5/3 : ℂ) (4/3)
      (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators)
    Matrix.trace ((H-boundaryOccupation)*
      twoSiteKreinData.diracAdjoint (H-boundaryOccupation)) = (-64/9 : ℂ) := by
  have hn : (5/3 : ℂ)*(5/3)-(4/3)*(4/3)=1 := by norm_num
  have hu : star (5/3 : ℂ) = 5/3 := by simp
  have hv : star (4/3 : ℂ) = 4/3 := by simp
  dsimp only
  rw [displacement_dirac_trace (5/3) (4/3) hn hu hv]
  norm_num

end InfoGeometry.Canonical.KitaevHyperbolicTrace

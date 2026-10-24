/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixTwoNoncommutativity
import InfoGeometry.Canonical.KitaevRotorMatrix
import InfoGeometry.Canonical.KitaevBoundaryFaithful
import InfoGeometry.Canonical.KitaevConcreteBoundary

/-! The native elliptic rotor and its movingPlus operator under the constructed
Krein adjoint. Fixed-metric selfadjointness is separate from idempotence. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevRotorDirac
open InfoGeometry.Quantum.KitaevChain
open KitaevBoundaryDiracPair KitaevBoundaryAlgebra KitaevBoundaryFaithful
open KitaevBoundaryConstructedMetric KitaevRotorMatrix ReflexiveNilpotentFlows PeirceRotorAction
variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] {N : ℕ}
variable (hN : 0 < N) (ops : MajoranaCliffordOperators N A)
variable (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
variable (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops)

theorem boundary_rotor_dirac (c s : ℂ) :
    (endpointKreinData hN ops hL hR).diracAdjoint
        (ReflexiveNilpotentFlows.rotor c s (boundaryAnnihilation hN ops) (boundaryCreation hN ops)) =
      ReflexiveNilpotentFlows.rotor (star c) (star s)
        (boundaryAnnihilation hN ops) (boundaryCreation hN ops) := by
  rw [boundary_rotor_eq_matrix, boundaryMatrixHom_dirac, boundary_rotor_eq_matrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairDiracMetric, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem boundary_movingPlus_dirac (c s : ℂ) :
    (endpointKreinData hN ops hL hR).diracAdjoint
        (movingPlus c s (boundaryAnnihilation hN ops) (boundaryCreation hN ops)) =
      movingPlus (star c) (-star s) (boundaryAnnihilation hN ops) (boundaryCreation hN ops) := by
  rw [boundary_movingPlus_eq_matrix, boundaryMatrixHom_dirac, boundary_movingPlus_eq_matrix]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairDiracMetric, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem boundary_movingPlus_dirac_fixed_iff [Nontrivial A] (c s : ℂ)
    (hc : star c = c) (hs : star s = s) :
    (endpointKreinData hN ops hL hR).diracAdjoint
        (movingPlus c s (boundaryAnnihilation hN ops) (boundaryCreation hN ops)) =
      movingPlus c s (boundaryAnnihilation hN ops) (boundaryCreation hN ops) ↔ c*s=0 := by
  rw [boundary_movingPlus_dirac, hc, hs, boundary_movingPlus_eq_matrix,
    boundary_movingPlus_eq_matrix, (boundaryMatrixHom_injective hN ops).eq_iff]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simp at h01
    linear_combination (1/2 : ℂ) * h01
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]

open KitaevConcreteBoundary

/-- A normalized circular parameter gives a genuine idempotent. -/
theorem twoSite_rotated_idempotent :
    IsIdempotentElem (movingPlus (3/5 : ℂ) (4/5 : ℂ)
      (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators)) := by
  exact movingPlus_idempotent (boundaryAnnihilation_sq (by decide) twoSiteOperators)
    (boundaryCreation_sq (by decide) twoSiteOperators)
    (boundary_reflexive (by decide) twoSiteOperators).1
    (boundary_reflexive (by decide) twoSiteOperators).2 _ _ (by norm_num)

/-- That idempotent is not selfadjoint for the unchanged constructed metric. -/
theorem twoSite_rotated_not_dirac_fixed :
    twoSiteKreinData.diracAdjoint (movingPlus (3/5 : ℂ) (4/5 : ℂ)
      (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators)) ≠
    movingPlus (3/5 : ℂ) (4/5 : ℂ)
      (boundaryAnnihilation (by decide) twoSiteOperators)
      (boundaryCreation (by decide) twoSiteOperators) := by
  have h := boundary_movingPlus_dirac_fixed_iff (by decide) twoSiteOperators
    (twoSite_star 0) (twoSite_star 3) (3/5 : ℂ) (4/5 : ℂ) (by norm_num) (by norm_num)
  simpa [twoSiteKreinData] using h

end InfoGeometry.Canonical.KitaevRotorDirac

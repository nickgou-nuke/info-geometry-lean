/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryConstructedMetric
import InfoGeometry.Canonical.KitaevBoundaryKrein
import InfoGeometry.Canonical.KitaevBoundaryDiracConservation

/-! The actual boundary occupation product is a conserved metric-compatible
idempotent, and recovers the constructed endpoint metric with its exact sign. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevBoundaryPeirce

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Algebra.GogberashviliNilpotentCARBridge
open KitaevBoundaryDiracPair KitaevBoundaryConstructedMetric
open KitaevBoundaryKrein KitaevBoundaryDiracConservation

variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}
variable (hN : 0 < N) (ops : MajoranaCliffordOperators N A)

theorem boundary_product_eq_DMinus :
    boundaryAnnihilation hN ops * boundaryCreation hN ops =
      DMinus (K := ℂ) (endpointMetric hN ops) := by
  rw [boundaryAnnihilation_eq_GPlus, boundaryCreation_eq_GMinus]
  apply GPlus_mul_GMinus (by norm_num) _ _ _
    (leftEndpoint_sq hN ops) (phased_rightEndpoint_sq hN ops)
    (eq_neg_of_add_eq_zero_right (endpoint_split_anticomm hN ops))
  simp [endpointMetric, mul_smul_comm]

theorem endpointMetric_eq_one_sub_two_boundary_product :
    endpointMetric hN ops =
      1 - 2 • (boundaryAnnihilation hN ops * boundaryCreation hN ops) := by
  rw [boundary_product_eq_DMinus]
  simp only [DMinus, two_nsmul]
  module

theorem boundary_product_idempotent :
    IsIdempotentElem (boundaryAnnihilation hN ops * boundaryCreation hN ops) := by
  change (boundaryAnnihilation hN ops * boundaryCreation hN ops) *
    (boundaryAnnihilation hN ops * boundaryCreation hN ops) = _
  calc
    _ = (boundaryAnnihilation hN ops * boundaryCreation hN ops *
        boundaryAnnihilation hN ops) * boundaryCreation hN ops := by noncomm_ring
    _ = _ := by rw [(boundary_reflexive hN ops).1]

theorem boundary_product_commutes (t : ℂ) :
    Commute (boundaryAnnihilation hN ops * boundaryCreation hN ops)
      (sweetSpotHamiltonian ops.toMajoranaOperators (algebraMap ℂ A t)) :=
  (boundaryAnnihilation_commutes hN ops t).mul_left (boundaryCreation_commutes hN ops t)

variable [StarRing A] [StarModule ℂ A]

theorem boundary_product_dirac_fixed
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops)
    (hR : star (rightEndpoint hN ops) = rightEndpoint hN ops) :
    (endpointKreinData hN ops hL hR).diracAdjoint
        (boundaryAnnihilation hN ops * boundaryCreation hN ops) =
      boundaryAnnihilation hN ops * boundaryCreation hN ops := by
  rw [InfoGeometry.Physics.KasparovKreinData.diracAdjoint_mul]
  rw [boundaryCreation_dirac_of_negative hN ops _
      (endpointKreinData_left_negative hN ops hL hR)
      (endpointKreinData_right_negative hN ops hL hR),
    boundaryAnnihilation_dirac_of_negative hN ops _
      (endpointKreinData_left_negative hN ops hL hR)
      (endpointKreinData_right_negative hN ops hL hR), neg_mul_neg]

end InfoGeometry.Canonical.KitaevBoundaryPeirce

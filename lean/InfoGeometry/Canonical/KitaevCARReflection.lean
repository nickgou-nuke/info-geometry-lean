/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARReflectionSector
import InfoGeometry.Canonical.KitaevBoundaryConstructedMetric
import InfoGeometry.Canonical.KitaevConcreteBoundary

/-! The actual Kitaev boundary pair supplies the CAR module obstruction.
Its endpoint reflection reverses the constructed indefinite pairing. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevCARReflection
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Topology.FractalCantorFock
open InfoGeometry.Algebra.GogberashviliNilpotentCARBridge
open KitaevBoundaryDiracPair KitaevBoundaryConstructedMetric
variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}
variable (hN : 0 < N) (ops : MajoranaCliffordOperators N A)

/-- Reuse the existing CAR interface for the native endpoint operators. -/
def boundaryCARPair : RealCARPair A where
  annihilation := boundaryAnnihilation hN ops
  creation := boundaryCreation hN ops
  nilpotent_annihilation := boundaryAnnihilation_sq hN ops
  nilpotent_creation := boundaryCreation_sq hN ops
  car := boundary_CAR hN ops

theorem reflection_eq_leftEndpoint :
    boundaryAnnihilation hN ops + boundaryCreation hN ops = leftEndpoint hN ops := by
  rw [boundaryAnnihilation_eq_GPlus, boundaryCreation_eq_GMinus]
  unfold GPlus GMinus
  module

theorem endpoint_fixed_sector_eq_zero {V : Type*} [AddCommMonoid V] [Module A V]
    (x : V) (hp : (boundaryAnnihilation hN ops * boundaryCreation hN ops) • x = x)
    (hq : leftEndpoint hN ops • x = x) : x = 0 := by
  apply (boundaryCARPair hN ops).reflection_fixed_sector_eq_zero x hp
  change (boundaryAnnihilation hN ops + boundaryCreation hN ops) • x = x
  simpa only [reflection_eq_leftEndpoint] using hq

theorem endpoint_reverses_metric :
    leftEndpoint hN ops * endpointMetric hN ops * leftEndpoint hN ops =
      -endpointMetric hN ops := by
  unfold endpointMetric
  rw [mul_smul_comm, smul_mul_assoc]
  have he : leftEndpoint hN ops * (leftEndpoint hN ops * rightEndpoint hN ops) *
      leftEndpoint hN ops = -(leftEndpoint hN ops * rightEndpoint hN ops) := by
    rw [← mul_assoc, leftEndpoint_sq, one_mul, endpoint_reverse]
  rw [he, smul_neg]

variable [StarRing A]

/-- The sign concerns the Dirac bra with metric eta, not the ordinary star pairing. -/
theorem endpoint_reverses_dirac_pairing
    (hL : star (leftEndpoint hN ops) = leftEndpoint hN ops) (x y : A) :
    star (leftEndpoint hN ops * x) * endpointMetric hN ops * (leftEndpoint hN ops * y) =
      -(star x * endpointMetric hN ops * y) := by
  rw [star_mul, hL]
  calc
    _ = star x * (leftEndpoint hN ops * endpointMetric hN ops * leftEndpoint hN ops) * y :=
      by simp only [mul_assoc]
    _ = _ := by rw [endpoint_reverses_metric]; simp only [mul_neg, neg_mul]

/-- The concrete two-site Jordan--Wigner matrices discharge the star hypothesis. -/
theorem twoSite_reflection_pairing (x y : CARMajoranaFiniteBridge.ChainOp) :
    let L := leftEndpoint (by decide) KitaevConcreteBoundary.twoSiteOperators
    star (L * x) * KitaevConcreteBoundary.twoSiteKreinData.eta * (L * y) =
      -(star x * KitaevConcreteBoundary.twoSiteKreinData.eta * y) := by
  exact endpoint_reverses_dirac_pairing (by decide)
    KitaevConcreteBoundary.twoSiteOperators (KitaevConcreteBoundary.twoSite_star 0) x y

end InfoGeometry.Canonical.KitaevCARReflection

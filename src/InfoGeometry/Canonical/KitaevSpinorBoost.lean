/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevHyperbolicDirac
import InfoGeometry.Canonical.SpinorialCore.KreinIncidence

/-! The existing unit-valued Kitaev boost acts by isometries of the scalar
Dirac pairing. Its metric bra transforms with the inverse, not with an
unqualified ordinary-adjoint identification. -/
noncomputable section
namespace InfoGeometry.Physics.KasparovKreinData
variable {A : Type*} [Ring A] [StarRing A]

theorem unit_isometry_of_dirac_inverse (K : KasparovKreinData A) (U : Aˣ)
    (h : K.diracAdjoint (U : A) = (↑U⁻¹ : A)) :
    star (U : A) * K.eta * (U : A) = K.eta := by
  change K.eta * star (U : A) * K.eta = (↑U⁻¹ : A) at h
  have he : K.eta * K.eta = 1 := K.2.1
  calc
    _ = K.eta * (K.eta * star (U : A) * K.eta) * (U : A) := by
      simp only [← mul_assoc, he, one_mul]
    _ = K.eta * (↑U⁻¹ : A) * (U : A) := by rw [h]
    _ = K.eta := by rw [mul_assoc, U.inv_mul, mul_one]

end InfoGeometry.Physics.KasparovKreinData

namespace InfoGeometry.Canonical.KitaevSpinorBoost
open Matrix KitaevHyperbolicDirac KitaevConcreteBoundary SpinorialCore.Krein
open CARMajoranaFiniteBridge

theorem boost_isometry (u v : ℂ) (h : u*u-v*v=1)
    (hu : star u=u) (hv : star v=v) :
    IsIsometry twoSiteKreinData.eta (twoSiteBoost u v h : ChainOp) :=
  twoSiteKreinData.unit_isometry_of_dirac_inverse _
    (twoSiteBoost_dirac_inverse u v h hu hv)

theorem boost_preserves_pairing (u v : ℂ) (h : u*u-v*v=1)
    (hu : star u=u) (hv : star v=v) (x y : (Fin 2 × Fin 2) → ℂ) :
    SpinorialCore.Krein.pairing twoSiteKreinData.eta
      ((twoSiteBoost u v h : ChainOp) *ᵥ x) ((twoSiteBoost u v h : ChainOp) *ᵥ y) =
      SpinorialCore.Krein.pairing twoSiteKreinData.eta x y :=
  pairing_isometry _ _ (boost_isometry u v h hu hv) x y

/-- Evaluate the transformed metric covector on an arbitrary state. -/
theorem boost_metricDual_inverse (u v : ℂ) (h : u*u-v*v=1)
    (hu : star u=u) (hv : star v=v) (x y : (Fin 2 × Fin 2) → ℂ) :
    SpinorialCore.Krein.metricDual twoSiteKreinData.eta ((twoSiteBoost u v h : ChainOp) *ᵥ x) y =
      SpinorialCore.Krein.metricDual twoSiteKreinData.eta x
        ((↑(twoSiteBoost u v h)⁻¹ : ChainOp) *ᵥ y) := by
  have hp := boost_preserves_pairing u v h hu hv x
    ((↑(twoSiteBoost u v h)⁻¹ : ChainOp) *ᵥ y)
  change SpinorialCore.Krein.pairing twoSiteKreinData.eta
    ((twoSiteBoost u v h : ChainOp) *ᵥ x) y =
    SpinorialCore.Krein.pairing twoSiteKreinData.eta x
      ((↑(twoSiteBoost u v h)⁻¹ : ChainOp) *ᵥ y)
  simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using hp

end InfoGeometry.Canonical.KitaevSpinorBoost

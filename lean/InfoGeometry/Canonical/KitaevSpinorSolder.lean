/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevSpinorBoost
import InfoGeometry.Canonical.KitaevSpinorReflection
import InfoGeometry.CliffordWeyl.DiracMetricCovariance

/-! The existing Dirac solder is the operator of rank at most one defined by the
existing scalar metric bra. Native boosts conjugate it, and reflection-fixed
spinors give square-zero solders through their indefinite nullity. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevSpinorSolder
open Matrix SpinorialCore.Krein
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open KitaevHyperbolicDirac KitaevConcreteBoundary KitaevBoundaryDiracPair
open CARMajoranaFiniteBridge
variable {n : Type*} [Fintype n]

theorem solder_action (J : Matrix n n ℂ) (x y z : n → ℂ) :
    solder J x y *ᵥ z = (SpinorialCore.Krein.metricDual J y z) • x := by
  change solder J x y *ᵥ z = (SpinorialCore.Krein.pairing J y z) • x
  simp only [solder, diracRow, vecMulVec_mulVec, dotProduct_mulVec,
    SpinorialCore.Krein.pairing, op_smul_eq_smul]

theorem boost_solder_conjugation (u v : ℂ) (h : u*u-v*v=1)
    (hu : star u=u) (hv : star v=v) (x y : (Fin 2 × Fin 2) → ℂ) :
    solder twoSiteKreinData.eta ((twoSiteBoost u v h : ChainOp) *ᵥ x)
      ((twoSiteBoost u v h : ChainOp) *ᵥ y) =
      (twoSiteBoost u v h : ChainOp) * solder twoSiteKreinData.eta x y *
        (↑(twoSiteBoost u v h)⁻¹ : ChainOp) := by
  have hi := KitaevSpinorBoost.boost_isometry u v h hu hv
  have he := congrArg (fun M : ChainOp => M * (↑(twoSiteBoost u v h)⁻¹ : ChainOp)) hi
  have hr : (twoSiteBoost u v h : ChainOp).conjTranspose * twoSiteKreinData.eta =
      twoSiteKreinData.eta * (↑(twoSiteBoost u v h)⁻¹ : ChainOp) := by
    simpa only [Matrix.star_eq_conjTranspose, mul_assoc, Units.mul_inv, mul_one] using he
  simp only [solder, diracRow, star_mulVec, vecMul_vecMul, hr,
    mul_vecMulVec, vecMulVec_mul]

theorem boost_solder_trace (u v : ℂ) (h : u*u-v*v=1)
    (hu : star u=u) (hv : star v=v) (x y : (Fin 2 × Fin 2) → ℂ) :
    Matrix.trace (solder twoSiteKreinData.eta ((twoSiteBoost u v h : ChainOp) *ᵥ x)
      ((twoSiteBoost u v h : ChainOp) *ᵥ y)) =
      Matrix.trace (solder twoSiteKreinData.eta x y) := by
  rw [boost_solder_conjugation u v h hu hv, Matrix.trace_mul_comm,
    ← mul_assoc, Units.inv_mul, one_mul]

theorem fixed_spinor_solder_sq_zero (x : (Fin 2 × Fin 2) → ℂ)
    (hx : (leftEndpoint (by decide) twoSiteOperators) *ᵥ x = x) :
    solder twoSiteKreinData.eta x x * solder twoSiteKreinData.eta x x = 0 := by
  rw [solder_quadratic]
  have hz := KitaevSpinorReflection.fixed_spinor_is_null x hx
  change SpinorialCore.Krein.pairing twoSiteKreinData.eta x x = 0 at hz
  have hr : diracRow twoSiteKreinData.eta x ⬝ᵥ x = 0 := by
    simpa only [diracRow, SpinorialCore.Krein.pairing, dotProduct_mulVec] using hz
  rw [hr, zero_smul]

end InfoGeometry.Canonical.KitaevSpinorSolder

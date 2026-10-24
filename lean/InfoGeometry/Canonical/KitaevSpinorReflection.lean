/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevCARReflection
import InfoGeometry.Canonical.SpinorialCore.KreinIncidence

/-! Scalar Dirac pairing of the actual two-site state vectors.
The endpoint reflection is an anti-isometry; its fixed vectors are null,
which is distinct from being zero in an indefinite metric. -/
noncomputable section
open Matrix
namespace InfoGeometry.Canonical.SpinorialCore.Krein
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem pairing_pullback (J U : Matrix n n ℂ) (x y : n → ℂ) :
    pairing J (U *ᵥ x) (U *ᵥ y) = pairing (U.conjTranspose * J * U) x y := by
  simp only [pairing, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem pairing_antiisometry (J U : Matrix n n ℂ)
    (h : U.conjTranspose * J * U = -J) (x y : n → ℂ) :
    pairing J (U *ᵥ x) (U *ᵥ y) = -pairing J x y := by
  rw [pairing_pullback, h]
  simp only [pairing, Matrix.neg_mulVec, dotProduct_neg]

end InfoGeometry.Canonical.SpinorialCore.Krein

namespace InfoGeometry.Canonical.KitaevSpinorReflection
open SpinorialCore.Krein KitaevBoundaryDiracPair KitaevConcreteBoundary
open KitaevCARReflection

theorem twoSite_scalar_pairing_reversal (x y : (Fin 2 × Fin 2) → ℂ) :
    SpinorialCore.Krein.pairing twoSiteKreinData.eta
      ((leftEndpoint (by decide) twoSiteOperators) *ᵥ x)
      ((leftEndpoint (by decide) twoSiteOperators) *ᵥ y) =
      -SpinorialCore.Krein.pairing twoSiteKreinData.eta x y := by
  apply pairing_antiisometry
  have hL : (leftEndpoint (by decide) twoSiteOperators).conjTranspose =
      leftEndpoint (by decide) twoSiteOperators := twoSite_star 0
  rw [hL]
  exact endpoint_reverses_metric (by decide) twoSiteOperators

theorem fixed_spinor_is_null (x : (Fin 2 × Fin 2) → ℂ)
    (hx : (leftEndpoint (by decide) twoSiteOperators) *ᵥ x = x) :
    metricDual twoSiteKreinData.eta x x = 0 := by
  have h := twoSite_scalar_pairing_reversal x x
  rw [hx] at h
  exact CharZero.eq_neg_self_iff.mp h

end InfoGeometry.Canonical.KitaevSpinorReflection

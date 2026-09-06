import Mathlib
import InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice

/-!
# Native polarized `(5,5)` boundary core

This owner keeps the finite quadratic carrier separate from Clifford
multiplication.  It is the rewrite boundary for the corresponding upstream
owner: only the coordinate quadratic facts are installed here.
-/

noncomputable section

namespace InfoGeometry.Clifford.PolarizedMinkowski55

open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice

abbrev Boundary55 := (ℝ × Minkowski13) × (ℝ × Minkowski13)

def boundaryQuadratic (z : Boundary55) : ℝ :=
  z.1.1 * z.2.1 - z.1.2.1 * z.2.2.1 +
    ∑ i : Fin 3, z.1.2.2 i * z.2.2.2 i

@[simp] theorem boundaryQuadratic_apply (z : Boundary55) :
    boundaryQuadratic z = z.1.1 * z.2.1 - z.1.2.1 * z.2.2.1 +
      ∑ i : Fin 3, z.1.2.2 i * z.2.2.2 i := rfl

def pairSwap : Boundary55 ≃ₗ[ℝ] Boundary55 where
  toFun z := (z.2, z.1)
  invFun z := (z.2, z.1)
  left_inv z := rfl
  right_inv z := rfl
  map_add' z w := rfl
  map_smul' c z := rfl

def vectorFlip : Boundary55 ≃ₗ[ℝ] Boundary55 where
  toFun z := ((z.1.1, -z.1.2), (z.2.1, -z.2.2))
  invFun z := ((z.1.1, -z.1.2), (z.2.1, -z.2.2))
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by
    ext <;> simp [neg_add, add_comm]
  map_smul' c z := by
    ext <;> simp

@[simp] theorem pairSwap_sq (z : Boundary55) : pairSwap (pairSwap z) = z := rfl

@[simp] theorem vectorFlip_sq (z : Boundary55) : vectorFlip (vectorFlip z) = z := by
  simp [vectorFlip]

theorem pairSwap_preserves (z : Boundary55) :
    boundaryQuadratic (pairSwap z) = boundaryQuadratic z := by
  simp [boundaryQuadratic, pairSwap, mul_comm]

theorem vectorFlip_preserves (z : Boundary55) :
    boundaryQuadratic (vectorFlip z) = boundaryQuadratic z := by
  simp [boundaryQuadratic, vectorFlip]

def mixedSwap : Boundary55 ≃ₗ[ℝ] Boundary55 := vectorFlip.trans pairSwap

@[simp] theorem mixedSwap_sq (z : Boundary55) : mixedSwap (mixedSwap z) = z := by
  change pairSwap (vectorFlip (pairSwap (vectorFlip z))) = z
  rw [show vectorFlip (pairSwap (vectorFlip z)) =
      pairSwap (vectorFlip (vectorFlip z)) by rfl]
  simp

theorem mixedSwap_preserves (z : Boundary55) :
    boundaryQuadratic (mixedSwap z) = boundaryQuadratic z := by
  change boundaryQuadratic (pairSwap (vectorFlip z)) = _
  rw [pairSwap_preserves, vectorFlip_preserves]

def alphaRay : Boundary55 := ((1, 0), (0, 0))
def betaRay : Boundary55 := ((0, 0), (1, 0))

@[simp] theorem alphaRay_null : boundaryQuadratic alphaRay = 0 := by simp [alphaRay]
@[simp] theorem betaRay_null : boundaryQuadratic betaRay = 0 := by simp [betaRay]

theorem boundary_finrank : Module.finrank ℝ Boundary55 = 10 := by
  simp [Boundary55, Minkowski13, Module.finrank_prod]

theorem left_half_null (a : ℝ) (u : Minkowski13) :
    boundaryQuadratic ((a, u), (0, 0)) = 0 := by simp [boundaryQuadratic]

theorem right_half_null (b : ℝ) (v : Minkowski13) :
    boundaryQuadratic ((0, 0), (b, v)) = 0 := by simp [boundaryQuadratic]

end InfoGeometry.Clifford.PolarizedMinkowski55

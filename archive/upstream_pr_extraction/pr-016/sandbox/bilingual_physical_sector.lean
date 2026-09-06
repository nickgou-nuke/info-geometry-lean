import InfoGeometry.Geometry.BilingualUpperHalfPlane
import InfoGeometry.Geometry.VerifiedCauchyKernel

/-!
# Sandbox: Bilingual Physical Sector and Cauchy Kernels
Defining the domain where the Cauchy kernel is constructively well-defined.
-/

noncomputable section

namespace InfoGeometry.Geometry.Sandbox

open InfoGeometry.Geometry
open InfoGeometry.Geometry.VerifiedCauchyKernel

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)}

/-- 
The Physical Sector of the Bilingual theory.
A point in the physical sector is a pair (Z, ζ) where Z is in the 
Bilingual Upper Half-Plane and ζ is a scalar parameter (e.g., on the boundary).
-/
structure PhysicalSector (D : ProjectivePolarizedBigradedBogoliubovDatum (E := E)) where
  /-- The operator point in the UHP -/
  Z : BilingualUpperHalfPlane D
  /-- The scalar parameter -/
  ζ : ℝ
  /-- Constructive witness that the kernel exists at this point -/
  kernel : VerifiedKernel D.K Z.tau ζ

/-- 
The UHP ensures that Z - ζ·1 has no kernel on the Hestenes real carrier,
as its imaginary part is strictly positive.
This is the "Physical" reason for the kernel's existence.
-/
theorem kernel_stability_under_perturbation
    (P : PhysicalSector D)
    (h_pos : ∀ v : DoubledSpace E, v ≠ 0 → ⟪v, D.K (P.Z.tau v)⟫_ℝ < 0) :
    ∀ v : DoubledSpace E, v ≠ 0 → (algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) P.ζ - P.Z.tau) v ≠ 0 := by
  intro v hv
  let A := algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) P.ζ - P.Z.tau
  intro h_null
  -- If A v = 0, then ζ v = Z v.
  have h_eq : (algebraMap ℝ (DoubledSpace E →L[ℝ] DoubledSpace E) P.ζ) v = P.Z.tau v := by
    rw [← sub_eq_zero] at h_null
    exact eq_of_sub_eq_zero h_null
  
  -- Then ⟪v, K(Zv)⟫ = ⟪v, K(ζv)⟫ = ζ ⟪v, Kv⟫.
  -- Since K is skew-adjoint, ⟪v, Kv⟫ = 0.
  have h_inner : ⟪v, D.K (P.Z.tau v)⟫_ℝ = 0 := by
    rw [← h_eq]
    simp only [ContinuousLinearMap.algebraMap_apply, id_eq, smul_eq_mul, 
               Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_apply, 
               ContinuousLinearMap.smul_apply]
    -- ⟪v, K(ζv)⟫ = ζ ⟪v, Kv⟫
    rw [map_smul, inner_smul_right]
    -- Since D.K is the Hestenes phase axis, it is skew-adjoint.
    -- (Actually, we need this hypothesis explicitly if not already in BogoliubovDatum)
    sorry -- Proof that ⟪v, Kv⟫ = 0 for skew-adjoint K.

  -- But h_pos says ⟪v, K(Zv)⟫ < 0 for v ≠ 0. Contradiction.
  have h_contra := h_pos v hv
  rw [h_inner] at h_contra
  exact (lt_irrefl 0) h_contra

end InfoGeometry.Geometry.Sandbox

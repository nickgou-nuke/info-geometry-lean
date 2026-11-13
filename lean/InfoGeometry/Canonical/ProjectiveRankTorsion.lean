/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ProjectiveFoundation
import Mathlib.LinearAlgebra.Determinant
import Mathlib.GroupTheory.OrderOfElement

/-!
# Rank annihilates the scalar projective multiplier class

The existing projective representation convention is
`P (g * h) = multiplier g h • (P g * P h)`.  On a finite-dimensional
vector space of dimension `r`, determinants therefore give
`det (P (g * h)) = multiplier g h ^ r * det (P g) * det (P h)`.
The inverse determinant is an explicit cochain whose coboundary is the
`r`th power of the multiplier.  Consequently `r` kills the multiplier
class in the existing native Mathlib `H2`.

The scalar field is commutative, but the linear operators need not commute.
Positive rank is needed for the finite-order conclusion; rank zero only
gives the vacuous annihilation identity.  This is an algebraic projective
representation theorem, not a theorem about spectral gaps or global gerbes.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRepresentation

variable {K G V : Type} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

attribute [local instance] trivialUnitsMulDistribMulAction

/-- Determinants detect the scalar multiplier with exponent the vector-space rank. -/
theorem det_toLinearMap_mul (P : ProjectiveRepresentation K G V) (g h : G) :
    LinearMap.det (P.toLinearEquiv (g * h)).toLinearMap =
      (P.multiplier g h : K) ^ Module.finrank K V *
        LinearMap.det (P.toLinearEquiv g).toLinearMap *
          LinearMap.det (P.toLinearEquiv h).toLinearMap := by
  have hop : (P.toLinearEquiv (g * h)).toLinearMap =
      (P.multiplier g h : K) •
        ((P.toLinearEquiv g).toLinearMap * (P.toLinearEquiv h).toLinearMap) := by
    ext x
    exact P.map_mul g h x
  rw [hop, LinearMap.det_smul, LinearMap.det.map_mul, mul_assoc]

/-- The same determinant identity in the group of scalar units. -/
theorem det_toLinearEquiv_mul (P : ProjectiveRepresentation K G V) (g h : G) :
    LinearEquiv.det (P.toLinearEquiv (g * h)) =
      P.multiplier g h ^ Module.finrank K V *
        LinearEquiv.det (P.toLinearEquiv g) *
          LinearEquiv.det (P.toLinearEquiv h) := by
  apply Units.ext
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, LinearEquiv.coe_det] using
    P.det_toLinearMap_mul g h

/-- The determinant cochain appropriate to the owner's multiplier convention. -/
def inverseDeterminantCochain (P : ProjectiveRepresentation K G V) : G → Kˣ :=
  fun g => (LinearEquiv.det (P.toLinearEquiv g))⁻¹

omit [FiniteDimensional K V] in
@[simp]
theorem inverseDeterminantCochain_one (P : ProjectiveRepresentation K G V) :
    P.inverseDeterminantCochain 1 = 1 := by
  simp [inverseDeterminantCochain, P.map_one]

/-- The inverse determinant gives an explicit coboundary, without commuting operators. -/
theorem inverseDeterminantCochain_coboundary
    (P : ProjectiveRepresentation K G V) (g h : G) :
    g • P.inverseDeterminantCochain h /
        P.inverseDeterminantCochain (g * h) * P.inverseDeterminantCochain g =
      P.multiplier g h ^ Module.finrank K V := by
  change (LinearEquiv.det (P.toLinearEquiv h))⁻¹ /
      (LinearEquiv.det (P.toLinearEquiv (g * h)))⁻¹ *
        (LinearEquiv.det (P.toLinearEquiv g))⁻¹ = _
  rw [P.det_toLinearEquiv_mul]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- The rank power of the multiplier is a multiplicative coboundary. -/
theorem multiplier_pow_finrank_isMulCoboundary₂
    (P : ProjectiveRepresentation K G V) :
    groupCohomology.IsMulCoboundary₂
      (fun p : G × G => P.multiplier p.1 p.2 ^ Module.finrank K V) :=
  ⟨P.inverseDeterminantCochain, P.inverseDeterminantCochain_coboundary⟩

omit [FiniteDimensional K V] in
/-- Scalar multiplication of the native cohomology class corresponds to
pointwise powers of its multiplicative cocycle representative. -/
theorem nsmul_multiplierClass_eq_zero_iff_isMulCoboundary₂
    (P : ProjectiveRepresentation K G V) (n : ℕ) :
    n • P.multiplierClass (G := G) (K := K) (V := V) = 0 ↔
      groupCohomology.IsMulCoboundary₂
        (fun p : G × G => P.multiplier p.1 p.2 ^ n) := by
  change n • groupCohomology.H2π (Rep.ofMulDistribMulAction G Kˣ)
    (P.multiplierToCocycles₂ (G := G) (K := K) (V := V)) = 0 ↔ _
  rw [← map_nsmul, groupCohomology.H2π_eq_zero_iff]
  have hcoe :
      (⇑(n • P.multiplierToCocycles₂ (G := G) (K := K) (V := V)) :
        G × G → Additive Kˣ) =
      Additive.ofMul ∘ (fun p : G × G => P.multiplier p.1 p.2 ^ n) := by
    funext p
    rfl
  rw [hcoe]
  constructor
  · intro h
    exact groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
      (M := Kˣ) (f := fun p : G × G => P.multiplier p.1 p.2 ^ n) h
  · intro h
    exact (groupCohomology.coboundariesOfIsMulCoboundary₂ h).property

/-- The dimension annihilates the actual native group-cohomology multiplier class. -/
theorem finrank_nsmul_multiplierClass_eq_zero
    (P : ProjectiveRepresentation K G V) :
    Module.finrank K V • P.multiplierClass (G := G) (K := K) (V := V) = 0 := by
  exact (P.nsmul_multiplierClass_eq_zero_iff_isMulCoboundary₂ _).mpr
    P.multiplier_pow_finrank_isMulCoboundary₂

/-- The additive order of the multiplier class divides the dimension. -/
theorem multiplierClass_addOrderOf_dvd_finrank
    (P : ProjectiveRepresentation K G V) :
    addOrderOf (P.multiplierClass (G := G) (K := K) (V := V)) ∣ Module.finrank K V :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mpr P.finrank_nsmul_multiplierClass_eq_zero

/-- A nonzero finite-dimensional projective carrier has a torsion multiplier class. -/
theorem multiplierClass_isOfFinAddOrder_of_finrank_pos
    (P : ProjectiveRepresentation K G V) (hr : 0 < Module.finrank K V) :
    IsOfFinAddOrder (P.multiplierClass (G := G) (K := K) (V := V)) := by
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨Module.finrank K V, hr, P.finrank_nsmul_multiplierClass_eq_zero⟩

end InfoGeometry.Canonical.ProjectiveFoundation.ProjectiveRepresentation

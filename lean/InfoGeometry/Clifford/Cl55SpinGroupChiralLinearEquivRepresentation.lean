import InfoGeometry.Clifford.Cl55SpinGroupRestrictedChiralRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Bundled invertibility of the restricted chiral Spin actions

The preceding owner provides monoid homomorphisms into `Module.End` on the two
chiral submodules.  This owner packages the same actions as `LinearEquiv`s.
It does not identify either submodule with an independently named spinor
carrier and makes no claim about a Spin-to-orthogonal kernel.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinGroupChiralLinearEquivRepresentation

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
open InfoGeometry.Clifford.Cl55SpinGroupRestrictedChiralRepresentation

noncomputable def chiralPlusRepresentationEquiv (g : Spin55) :
    chiralPlusSector ≃ₗ[ℝ] chiralPlusSector where
  toFun := chiralPlusRepresentation g
  invFun := chiralPlusRepresentation g⁻¹
  left_inv := by
    intro v
    change (chiralPlusRepresentation g⁻¹ * chiralPlusRepresentation g) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv := by
    intro v
    change (chiralPlusRepresentation g * chiralPlusRepresentation g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' := by
    intro v w
    exact map_add (chiralPlusRepresentation g) v w
  map_smul' := by
    intro a v
    exact map_smul (chiralPlusRepresentation g) a v

noncomputable def chiralMinusRepresentationEquiv (g : Spin55) :
    chiralMinusSector ≃ₗ[ℝ] chiralMinusSector where
  toFun := chiralMinusRepresentation g
  invFun := chiralMinusRepresentation g⁻¹
  left_inv := by
    intro v
    change (chiralMinusRepresentation g⁻¹ * chiralMinusRepresentation g) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv := by
    intro v
    change (chiralMinusRepresentation g * chiralMinusRepresentation g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' := by
    intro v w
    exact map_add (chiralMinusRepresentation g) v w
  map_smul' := by
    intro a v
    exact map_smul (chiralMinusRepresentation g) a v

@[simp] theorem chiralPlusRepresentationEquiv_apply
    (g : Spin55) (v : chiralPlusSector) :
    chiralPlusRepresentationEquiv g v = chiralPlusRepresentation g v :=
  rfl

@[simp] theorem chiralMinusRepresentationEquiv_apply
    (g : Spin55) (v : chiralMinusSector) :
    chiralMinusRepresentationEquiv g v = chiralMinusRepresentation g v :=
  rfl

theorem chiralPlusRepresentationEquiv_inverse
    (g : Spin55) :
    (chiralPlusRepresentationEquiv g).symm =
      chiralPlusRepresentationEquiv g⁻¹ := by
  ext v
  rfl

theorem chiralMinusRepresentationEquiv_inverse
    (g : Spin55) :
    (chiralMinusRepresentationEquiv g).symm =
      chiralMinusRepresentationEquiv g⁻¹ := by
  ext v
  rfl

noncomputable def chiralPlusLinearEquivRepresentation :
    Spin55 →* (chiralPlusSector ≃ₗ[ℝ] chiralPlusSector) where
  toFun := chiralPlusRepresentationEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change chiralPlusRepresentation (1 : Spin55) v = v
    simp
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    change chiralPlusRepresentation (g * h) v =
      (chiralPlusRepresentation g * chiralPlusRepresentation h) v
    rw [map_mul]

noncomputable def chiralMinusLinearEquivRepresentation :
    Spin55 →* (chiralMinusSector ≃ₗ[ℝ] chiralMinusSector) where
  toFun := chiralMinusRepresentationEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change chiralMinusRepresentation (1 : Spin55) v = v
    simp
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    change chiralMinusRepresentation (g * h) v =
      (chiralMinusRepresentation g * chiralMinusRepresentation h) v
    rw [map_mul]

@[simp] theorem chiralPlusLinearEquivRepresentation_apply
    (g : Spin55) :
    chiralPlusLinearEquivRepresentation g =
      chiralPlusRepresentationEquiv g :=
  rfl

@[simp] theorem chiralMinusLinearEquivRepresentation_apply
    (g : Spin55) :
    chiralMinusLinearEquivRepresentation g =
      chiralMinusRepresentationEquiv g :=
  rfl

end InfoGeometry.Clifford.Cl55SpinGroupChiralLinearEquivRepresentation

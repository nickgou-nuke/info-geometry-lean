import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornFieldSpectralReadout

/-!
# Complexified left-regular Zorn operator

The Zorn carrier is non-associative, so its field element is not assigned an
ordinary eigenvalue problem by notation alone.  This owner supplies the
canonical associative replacement: left multiplication is a complex-linear
map on the complexified eight-coordinate carrier.

The quadratic relation is proved at the linear-map level using the native
left-alternative law.  A concrete `8 × 8` matrix and its characteristic
polynomial require an additional finite-coordinate basis theorem and are not
silently identified with this operator.
-/

namespace InfoGeometry.Canonical.ZornComplexifiedLeftRegularSpectralBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.ZornFieldSpectralReadout

abbrev ComplexZorn := ZornVectorMatrix ℂ

/-- The associative linear operator obtained by left multiplication by `X`. -/
def leftRegular (X : ComplexZorn) : ComplexZorn →ₗ[ℂ] ComplexZorn where
  toFun := fun Y => mul X Y
  map_add' := by
    intro Y Z
    exact mul_add X Y Z
  map_smul' := by
    intro c Y
    exact mul_smul c X Y

@[simp] theorem leftRegular_apply (X Y : ComplexZorn) :
    leftRegular X Y = mul X Y :=
  rfl

theorem leftRegular_square (X Y : ComplexZorn) :
    leftRegular X (leftRegular X Y) = leftRegular (mul X X) Y := by
  change mul X (mul X Y) = mul (mul X X) Y
  have h := associator_left_alternative X Y
  change mul (mul X X) Y - mul X (mul X Y) = 0 at h
  exact (sub_eq_zero.mp h).symm

theorem leftRegular_square_of_scalar_square
    (X : ComplexZorn) (q : ℂ)
    (hX : mul X X = scalar q) (Y : ComplexZorn) :
    leftRegular X (leftRegular X Y) = smul q Y := by
  rw [leftRegular_square, hX]
  change mul (scalar q) Y = smul q Y
  exact scalar_mul q Y

theorem leftRegular_offDiagonal_square
    (u v : ZornVec3 ℂ) (Y : ComplexZorn) :
    leftRegular (offDiagonal u v)
        (leftRegular (offDiagonal u v) Y) =
      smul (dot u v) Y := by
  apply leftRegular_square_of_scalar_square (offDiagonal u v) (dot u v) _ Y
  exact ZornFieldSpectralReadout.offDiagonal_mul_self_eq_scalar_dot u v

theorem leftRegular_electricMagnetic_square
    (electric magnetic : ZornVec3 ℂ) (Y : ComplexZorn) :
    leftRegular
        (offDiagonal
          (fun i => -(electric i + magnetic i))
          (fun i => electric i - magnetic i))
        (leftRegular
          (offDiagonal
            (fun i => -(electric i + magnetic i))
            (fun i => electric i - magnetic i)) Y) =
      smul (dot magnetic magnetic - dot electric electric) Y := by
  apply leftRegular_square_of_scalar_square _
    (dot magnetic magnetic - dot electric electric) _ Y
  exact ZornFieldSpectralReadout.electricMagnetic_offDiagonal_square electric magnetic

end InfoGeometry.Canonical.ZornComplexifiedLeftRegularSpectralBridge

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornAlternativeLaws

noncomputable section

namespace InfoGeometry.Canonical.ZornInverseMoufangBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

variable {F : Type*} [Field F]

abbrev ZornF (F : Type*) [Field F] := ZornVectorMatrix F

/--
The norm-conjugate inverse formula on the field-valued Zorn carrier.

This is deliberately a named totalized operation rather than a global `Inv`
instance: when `norm X = 0`, the field convention gives `(norm X)⁻¹ = 0`, so
`totalizedInverse X = 0`; it is a genuine two-sided inverse only on the
non-isotropic locus.
-/
noncomputable def totalizedInverse (X : ZornF F) : ZornF F :=
  ZornVectorMatrix.smul (ZornVectorMatrix.norm X)⁻¹ (ZornVectorMatrix.conj X)

/-- The totalized inverse vanishes on the split null cone. -/
theorem totalizedInverse_of_norm_eq_zero
    (X : ZornF F) (hX : ZornVectorMatrix.norm X = 0) :
    totalizedInverse X = ZornVectorMatrix.zero := by
  rw [totalizedInverse, hX]
  rw [inv_zero]
  exact ZornVectorMatrix.zero_smul (R := F) _

/-- On the non-isotropic locus, the norm-conjugate formula is a left inverse. -/
theorem totalizedInverse_mul_self
    (X : ZornF F) (hX : ZornVectorMatrix.norm X ≠ 0) :
    ZornVectorMatrix.mul (totalizedInverse X) X = ZornVectorMatrix.one := by
  rw [totalizedInverse, ZornVectorMatrix.smul_mul]
  have hk : ZornVectorMatrix.mul (ZornVectorMatrix.conj X) X =
      ZornVectorMatrix.smul (ZornVectorMatrix.norm X) ZornVectorMatrix.one := by
    simpa only [ZornVectorMatrix.mul_one] using
      kirmse_left X ZornVectorMatrix.one
  rw [hk]
  have hscalar (Z : ZornF F) :
      ZornVectorMatrix.smul (ZornVectorMatrix.norm X)⁻¹
          (ZornVectorMatrix.smul (ZornVectorMatrix.norm X) Z) = Z := by
    apply ZornVectorMatrix.ext <;>
      simp [ZornVectorMatrix.smul] <;> field_simp [hX]
  exact hscalar ZornVectorMatrix.one

/-- On the non-isotropic locus, the norm-conjugate formula is a right inverse. -/
theorem self_mul_totalizedInverse
    (X : ZornF F) (hX : ZornVectorMatrix.norm X ≠ 0) :
    ZornVectorMatrix.mul X (totalizedInverse X) = ZornVectorMatrix.one := by
  rw [totalizedInverse, ZornVectorMatrix.mul_smul]
  have hk : ZornVectorMatrix.mul X (ZornVectorMatrix.conj X) =
      ZornVectorMatrix.smul (ZornVectorMatrix.norm X) ZornVectorMatrix.one := by
    simpa only [ZornVectorMatrix.one_mul] using
      kirmse_right X ZornVectorMatrix.one
  rw [hk]
  have hscalar (Z : ZornF F) :
      ZornVectorMatrix.smul (ZornVectorMatrix.norm X)⁻¹
          (ZornVectorMatrix.smul (ZornVectorMatrix.norm X) Z) = Z := by
    apply ZornVectorMatrix.ext <;>
      simp [ZornVectorMatrix.smul] <;> field_simp [hX]
  exact hscalar ZornVectorMatrix.one

/-- Kirmse cancellation gives the full left inverse property. -/
theorem totalizedInverse_mul_cancel_left
    (X Y : ZornF F) (hX : ZornVectorMatrix.norm X ≠ 0) :
    ZornVectorMatrix.mul (totalizedInverse X) (ZornVectorMatrix.mul X Y) = Y := by
  rw [totalizedInverse, ZornVectorMatrix.smul_mul, kirmse_left]
  have hscalar (Z : ZornF F) :
      ZornVectorMatrix.smul (ZornVectorMatrix.norm X)⁻¹
          (ZornVectorMatrix.smul (ZornVectorMatrix.norm X) Z) = Z := by
    apply ZornVectorMatrix.ext <;>
      simp [ZornVectorMatrix.smul] <;> field_simp [hX]
  exact hscalar Y

/-- Kirmse cancellation gives the full right inverse property. -/
theorem mul_totalizedInverse_cancel_right
    (X Y : ZornF F) (hX : ZornVectorMatrix.norm X ≠ 0) :
    ZornVectorMatrix.mul (ZornVectorMatrix.mul Y X) (totalizedInverse X) = Y := by
  rw [totalizedInverse, ZornVectorMatrix.mul_smul, kirmse_right]
  have hscalar (Z : ZornF F) :
      ZornVectorMatrix.smul (ZornVectorMatrix.norm X)⁻¹
          (ZornVectorMatrix.smul (ZornVectorMatrix.norm X) Z) = Z := by
    apply ZornVectorMatrix.ext <;>
      simp [ZornVectorMatrix.smul] <;> field_simp [hX]
  exact hscalar Y

/-- Conjugate-form Moufang reassociation supplied by the native Zorn laws.

The conjugate product is kept explicit: the totalized norm reciprocal is not
silently treated as an inverse on the split null cone.
-/
theorem inverse_moufang
    (X Y : ZornF F) :
    ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y)
        (ZornVectorMatrix.mul (ZornVectorMatrix.conj X) X) =
      ZornVectorMatrix.mul X
        (ZornVectorMatrix.mul (ZornVectorMatrix.mul Y (ZornVectorMatrix.conj X)) X) := by
  exact middle_moufang X Y (ZornVectorMatrix.conj X)

/-- Dual conjugate-form reassociation, also a native Moufang identity. -/
theorem inverse_moufang_dual
    (X Y : ZornF F) :
    ZornVectorMatrix.mul (ZornVectorMatrix.mul (ZornVectorMatrix.conj X) Y)
        (ZornVectorMatrix.mul X (ZornVectorMatrix.conj X)) =
      ZornVectorMatrix.mul (ZornVectorMatrix.conj X)
        (ZornVectorMatrix.mul (ZornVectorMatrix.mul Y X)
          (ZornVectorMatrix.conj X)) := by
  exact middle_moufang (ZornVectorMatrix.conj X) Y X

/-- The genuine invertible locus is exactly where the cancellation theorems apply. -/
def IsNonIsotropic (X : ZornF F) : Prop := ZornVectorMatrix.norm X ≠ 0

/-- Packet of the two-sided inverse laws on the non-isotropic locus. -/
theorem nonIsotropic_inverse_packet
    (X : ZornF F) (hX : IsNonIsotropic X) :
    ZornVectorMatrix.mul (totalizedInverse X) X = ZornVectorMatrix.one ∧
      ZornVectorMatrix.mul X (totalizedInverse X) = ZornVectorMatrix.one := by
  exact ⟨totalizedInverse_mul_self X hX, self_mul_totalizedInverse X hX⟩

end InfoGeometry.Canonical.ZornInverseMoufangBridge

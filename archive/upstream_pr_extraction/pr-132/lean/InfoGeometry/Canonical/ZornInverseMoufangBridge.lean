import Mathlib.Tactic
import InfoGeometry.Algebra.ZornAlternativeLaws

noncomputable section

namespace InfoGeometry.Canonical.ZornInverseMoufangBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

variable {F : Type*} [Field F]

abbrev ZornF := ZornVectorMatrix F

/--
The norm-conjugate inverse formula on the field-valued Zorn carrier.

This is deliberately a named totalized operation rather than a global `Inv`
instance: when `norm X = 0`, the field convention gives `(norm X)⁻¹ = 0`, so
`totalizedInverse X = 0`; it is a genuine two-sided inverse only on the
non-isotropic locus.
-/
noncomputable def totalizedInverse (X : ZornF) : ZornF :=
  smul (norm X)⁻¹ (conj X)

/-- The totalized inverse vanishes on the split null cone. -/
theorem totalizedInverse_of_norm_eq_zero
    (X : ZornF) (hX : norm X = 0) :
    totalizedInverse X = zero := by
  simp [totalizedInverse, hX, smul_zero]

/-- On the non-isotropic locus, the norm-conjugate formula is a left inverse. -/
theorem totalizedInverse_mul_self
    (X : ZornF) (hX : norm X ≠ 0) :
    mul (totalizedInverse X) X = one := by
  rw [totalizedInverse, smul_mul]
  have hk : mul (conj X) X = smul (norm X) one := by
    simpa only [mul_one] using kirmse_left X one
  rw [hk]
  ext i <;> try fin_cases i <;>
    simp [smul, one, hX]

/-- On the non-isotropic locus, the norm-conjugate formula is a right inverse. -/
theorem self_mul_totalizedInverse
    (X : ZornF) (hX : norm X ≠ 0) :
    mul X (totalizedInverse X) = one := by
  rw [totalizedInverse, mul_smul]
  have hk : mul X (conj X) = smul (norm X) one := by
    simpa only [mul_one] using kirmse_right X one
  rw [hk]
  ext i <;> try fin_cases i <;>
    simp [smul, one, hX]

/-- Kirmse cancellation gives the full left inverse property. -/
theorem totalizedInverse_mul_cancel_left
    (X Y : ZornF) (hX : norm X ≠ 0) :
    mul (totalizedInverse X) (mul X Y) = Y := by
  rw [totalizedInverse, smul_mul, kirmse_left]
  ext i <;> try fin_cases i <;>
    simp [smul, hX]

/-- Kirmse cancellation gives the full right inverse property. -/
theorem mul_totalizedInverse_cancel_right
    (X Y : ZornF) (hX : norm X ≠ 0) :
    mul (mul Y X) (totalizedInverse X) = Y := by
  rw [totalizedInverse, mul_smul, kirmse_right]
  ext i <;> try fin_cases i <;>
    simp [smul, hX]

/--
Inverse-Moufang reassociation.  This identity is unconditional because the
norm reciprocal occurs only as a central scalar coefficient; at `norm X = 0`
both sides use the totalized value `0`.
-/
theorem inverse_moufang
    (X Y : ZornF) :
    mul (mul X Y) (totalizedInverse X) =
      mul X (mul Y (totalizedInverse X)) := by
  ext i <;> try fin_cases i <;>
    simp [totalizedInverse, mul, smul, conj, norm,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
    ring

/-- Dual inverse-Moufang reassociation. -/
theorem inverse_moufang_dual
    (X Y : ZornF) :
    mul (totalizedInverse X) (mul Y X) =
      mul (mul (totalizedInverse X) Y) X := by
  ext i <;> try fin_cases i <;>
    simp [totalizedInverse, mul, smul, conj, norm,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
    ring

/-- The genuine invertible locus is exactly where the cancellation theorems apply. -/
def IsNonIsotropic (X : ZornF) : Prop := norm X ≠ 0

/-- Packet of the two-sided inverse laws on the non-isotropic locus. -/
theorem nonIsotropic_inverse_packet
    (X : ZornF) (hX : IsNonIsotropic X) :
    mul (totalizedInverse X) X = one ∧
      mul X (totalizedInverse X) = one := by
  exact ⟨totalizedInverse_mul_self X hX, self_mul_totalizedInverse X hX⟩

end InfoGeometry.Canonical.ZornInverseMoufangBridge

import InfoGeometry.Canonical.ZornIntegralSpinSubgroup

/-!
# Integral Zorn, real spin, and triality closure

This file maps the external construction of the integral spin triality closure
onto the canonical polymorphic types. Since `ZornMatrix` is polymorphic,
triality and multiplication automatically commute with scalar extension via
`zornBaseChange`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Canonical.ZornIntegralSpinSubgroup

variable {R : Type*} [CommRing R]

attribute [local simp] Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ Pi.smul_apply Pi.add_apply Pi.sub_apply Pi.neg_apply

/-- Cyclic coordinate triality on the generic Zorn matrix carrier. -/
def zornTriality (Z : ZornMatrix R) : ZornMatrix R where
  a := Z.a
  b := Z.b
  x := ![Z.x 1, Z.x 2, Z.x 0]
  y := ![Z.y 1, Z.y 2, Z.y 0]

theorem zornTriality_order_three (Z : ZornMatrix R) :
    zornTriality (zornTriality (zornTriality Z)) = Z := by
  apply ZornMatrix.ext
  · rfl
  · rfl
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl

theorem zornTriality_norm (Z : ZornMatrix R) :
    zornNorm (zornTriality Z) = zornNorm Z := by
  simp [zornTriality, zornNorm_apply, zornNormFun, dot]
  ring

theorem zornTriality_mul (X Y : ZornMatrix R) :
    zornTriality (X * Y) = zornTriality X * zornTriality Y := by
  apply ZornMatrix.ext
  · simp [zornTriality, mul_def, mul, dot, cross]; ring
  · simp [zornTriality, mul_def, mul, dot, cross]; ring
  · ext i
    fin_cases i <;> simp [zornTriality, mul_def, mul, dot, cross]
  · ext i
    fin_cases i <;> simp [zornTriality, mul_def, mul, dot, cross]

/-! ## Scalar extension compatibility -/

theorem zornBaseChange_mul (X Y : ZornMatrix ℤ) :
    zornBaseChange (X * Y) = zornBaseChange X * zornBaseChange Y := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]
  · simp [mul_def, mul, dot, cross]
  · ext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]
  · ext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]

theorem zornBaseChange_triality (X : ZornMatrix ℤ) :
    zornBaseChange (zornTriality X) = zornTriality (zornBaseChange X) := by
  apply ZornMatrix.ext
  · rfl
  · rfl
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl

/-- The comprehensive closure theorem replacing the ad-hoc coordinate bridges.
The integral Zorn matrices faithfully embed into the real Zorn carrier preserving
the norm, multiplication, and triality. -/
theorem integral_spin_triality_closure (X Y : ZornMatrix ℤ) :
    zornNorm (R := ℝ) (zornBaseChange X) = (zornNorm (R := ℤ) X : ℝ) ∧
    zornBaseChange (X * Y) = zornBaseChange X * zornBaseChange Y ∧
    zornBaseChange (zornTriality X) = zornTriality (zornBaseChange X) := by
  exact ⟨zornBaseChange_zornNorm X, zornBaseChange_mul X Y, zornBaseChange_triality X⟩

end InfoGeometry.Canonical.ZornIntegralSpinTrialityClosure

end noncomputable section

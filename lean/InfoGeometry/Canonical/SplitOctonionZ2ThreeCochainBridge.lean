import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib

namespace InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge
open InfoGeometry.Canonical

abbrev Grade := Fin 3 → ZMod 2
def gradeAdd (x y : Grade) : Grade := fun i => x i + y i
@[simp] theorem gradeAdd_apply (x y : Grade) (i : Fin 3) : gradeAdd x y i = x i + y i := rfl

def basisOfIndex : Fin 8 → IntegralSplitBasis := ![.one, .l, .i, .il, .j, .jl, .k, .kl]
def gradeOfBasis : IntegralSplitBasis → Grade
  | .one => ![0, 0, 0] | .l => ![1, 0, 0] | .i => ![0, 1, 0] | .il => ![1, 1, 0]
  | .j => ![0, 0, 1] | .jl => ![1, 0, 1] | .k => ![0, 1, 1] | .kl => ![1, 1, 1]
def gradeIndex (x : Grade) : Fin 8 :=
  ⟨(x 0).val + 2 * (x 1).val + 4 * (x 2).val, by
    have h0 : (x 0).val < 2 := (x 0).isLt
    have h1 : (x 1).val < 2 := (x 1).isLt
    have h2 : (x 2).val < 2 := (x 2).isLt
    omega⟩
def basisOfGrade (x : Grade) : IntegralSplitBasis := basisOfIndex (gradeIndex x)
@[simp] theorem basisOfGrade_gradeOfBasis (b : IntegralSplitBasis) : basisOfGrade (gradeOfBasis b) = b := by
  cases b <;> rfl

/-- The executable Cayley--Dickson multiplication and the explicit basis table
are not interchangeable without an additional convention-compatibility
theorem.  This finite discrepancy records that the two current implementations
do not agree on every basis pair. -/
theorem splitOctonionMul_basisMul_not_universal :
    ∃ p q : IntegralSplitBasis,
      splitOctonionMul (splitBasisVector p) (splitBasisVector q) ≠ basisMul p q := by
  native_decide

def cochainF (x y : Grade) : ℚ :=
  (basisMul (basisOfGrade x) (basisOfGrade y)) (basisOfGrade (gradeAdd x y))
theorem cochainF_values (x y : Grade) : cochainF x y = 1 ∨ cochainF x y = -1 := by
  revert x y
  native_decide
theorem cochainF_ne_zero (x y : Grade) : cochainF x y ≠ 0 := by
  rcases cochainF_values x y with h | h <;> simp [h]
theorem native_basisMul_is_cochainF (x y : Grade) :
    (fun b => (basisMul (basisOfGrade x) (basisOfGrade y) b : ℚ)) =
      cochainF x y • (fun b => (splitBasisVector (basisOfGrade (gradeAdd x y)) b : ℚ)) := by
  revert x y
  native_decide
theorem cochainF_one_left (x : Grade) : cochainF (gradeOfBasis .one) x = 1 := by
  revert x
  native_decide
theorem cochainF_one_right (x : Grade) : cochainF x (gradeOfBasis .one) = 1 := by
  revert x
  native_decide

def associatorCochain (x y z : Grade) : ℚ :=
  cochainF x y * cochainF (gradeAdd x y) z / (cochainF y z * cochainF x (gradeAdd y z))
def exchangeCochain (x y : Grade) : ℚ := cochainF x y / cochainF y x

theorem cochain_reassociation_identity (x y z : Grade) :
    cochainF x y * cochainF (gradeAdd x y) z =
      associatorCochain x y z *
        (cochainF y z * cochainF x (gradeAdd y z)) := by
  unfold associatorCochain
  field_simp [cochainF_ne_zero]

theorem associatorCochain_sq (x y z : Grade) :
    associatorCochain x y z * associatorCochain x y z = 1 := by
  unfold associatorCochain
  have hxy : cochainF x y * cochainF (gradeAdd x y) z ≠ 0 :=
    mul_ne_zero (cochainF_ne_zero _ _) (cochainF_ne_zero _ _)
  have hyz : cochainF y z * cochainF x (gradeAdd y z) ≠ 0 :=
    mul_ne_zero (cochainF_ne_zero _ _) (cochainF_ne_zero _ _)
  have h1 : cochainF x y * cochainF (gradeAdd x y) z = 1 ∨
      cochainF x y * cochainF (gradeAdd x y) z = -1 := by
    rcases cochainF_values x y with hxy' | hxy' <;>
      rcases cochainF_values (gradeAdd x y) z with hxyz' | hxyz' <;>
      simp [hxy', hxyz']
  have h2 : cochainF y z * cochainF x (gradeAdd y z) = 1 ∨
      cochainF y z * cochainF x (gradeAdd y z) = -1 := by
    rcases cochainF_values y z with hyz' | hyz' <;>
      rcases cochainF_values x (gradeAdd y z) with hxyz' | hxyz' <;>
      simp [hyz', hxyz']
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h1, h2]

theorem exchangeCochain_sq (x y : Grade) :
    exchangeCochain x y * exchangeCochain x y = 1 := by
  unfold exchangeCochain
  have hxy : cochainF x y ≠ 0 := cochainF_ne_zero x y
  have hyx : cochainF y x ≠ 0 := cochainF_ne_zero y x
  have h1 : cochainF x y = 1 ∨ cochainF x y = -1 := cochainF_values x y
  have h2 : cochainF y x = 1 ∨ cochainF y x = -1 := cochainF_values y x
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h1, h2]
theorem native_associator_three_cocycle (x y z w : Grade) :
    associatorCochain y z w * associatorCochain x (gradeAdd y z) w * associatorCochain x y z =
      associatorCochain (gradeAdd x y) z w * associatorCochain x y (gradeAdd z w) := by
  revert x y z w
  native_decide
theorem native_exchange_is_cochain (x y : Grade) :
    cochainF x y = exchangeCochain x y * cochainF y x := by
  unfold exchangeCochain
  rw [div_mul_cancel₀ _ (cochainF_ne_zero y x)]

end InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge

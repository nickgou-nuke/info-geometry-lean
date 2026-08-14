import re

content = """import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import Mathlib

/-!
# Finite `((ZMod 2)^3)` cochain readout of the native split-octonion table

This owner is deliberately finite.  It records the eight native basis labels
as three-bit grades, extracts the sign of each tabulated basis product, and
proves the resulting finite associator and exchange formulas by computation.
It does not assert a quasi-Hopf structure, an infinite boundary, or a
categorical equivalence.
-/

namespace InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge

open InfoGeometry.Canonical

abbrev Grade := Fin 3 → ZMod 2

def gradeAdd (x y : Grade) : Grade := fun i => x i + y i

@[simp] theorem gradeAdd_apply (x y : Grade) (i : Fin 3) :
    gradeAdd x y i = x i + y i := rfl

def basisOfIndex : Fin 8 → IntegralSplitBasis :=
  ![.one, .l, .i, .il, .j, .jl, .k, .kl]

def gradeOfBasis : IntegralSplitBasis → Grade
  | .one => ![0, 0, 0]
  | .l   => ![1, 0, 0]
  | .i   => ![0, 1, 0]
  | .il  => ![1, 1, 0]
  | .j   => ![0, 0, 1]
  | .jl  => ![1, 0, 1]
  | .k   => ![0, 1, 1]
  | .kl  => ![1, 1, 1]

def gradeIndex (x : Grade) : Fin 8 :=
  ⟨(x 0).val + 2 * (x 1).val + 4 * (x 2).val, by
    have h0 : (x 0).val < 2 := (x 0).isLt
    have h1 : (x 1).val < 2 := (x 1).isLt
    have h2 : (x 2).val < 2 := (x 2).isLt
    omega⟩

def basisOfGrade (x : Grade) : IntegralSplitBasis :=
  basisOfIndex (gradeIndex x)

@[simp] theorem basisOfGrade_gradeOfBasis (b : IntegralSplitBasis) :
    basisOfGrade (gradeOfBasis b) = b := by
  cases b <;> rfl

def cochainF (x y : Grade) : ℚ :=
  (basisMul (basisOfGrade x) (basisOfGrade y))
    (basisOfGrade (gradeAdd x y))

theorem cochainF_values (x y : Grade) : cochainF x y = 1 ∨ cochainF x y = -1 := by
  revert x y
  native_decide

theorem cochainF_ne_zero (x y : Grade) : cochainF x y ≠ 0 := by
  rcases cochainF_values x y with h | h <;> simp [h]

def associatorCochain (x y z : Grade) : ℚ :=
  cochainF x y * cochainF (gradeAdd x y) z /
    (cochainF y z * cochainF x (gradeAdd y z))

def exchangeCochain (x y : Grade) : ℚ :=
  cochainF x y / cochainF y x

theorem native_basisMul_is_cochainF (x y : Grade) :
    (fun b => (basisMul (basisOfGrade x) (basisOfGrade y) b : ℚ)) =
      cochainF x y •
        (fun b =>
          (splitBasisVector (basisOfGrade (gradeAdd x y)) b : ℚ)) := by
  revert x y
  native_decide

theorem cochainF_one_left (x : Grade) :
    cochainF (gradeOfBasis .one) x = 1 := by
  revert x
  native_decide

theorem cochainF_one_right (x : Grade) :
    cochainF x (gradeOfBasis .one) = 1 := by
  revert x
  native_decide

theorem native_associator_three_cocycle (x y z w : Grade) :
    associatorCochain y z w * associatorCochain x (gradeAdd y z) w *
        associatorCochain x y z =
      associatorCochain (gradeAdd x y) z w *
        associatorCochain x y (gradeAdd z w) := by
  revert x y z w
  native_decide

theorem native_exchange_is_cochain (x y : Grade) :
    cochainF x y = exchangeCochain x y * cochainF y x := by
  unfold exchangeCochain
  have hz : cochainF y x ≠ 0 := cochainF_ne_zero y x
  rw [div_mul_cancel₀ _ hz]

/-- The multiplicative associativity defect 3-cocycle derived from `cochainF`. -/
def splitAssociativityCocycle (x y z : Grade) : ℚ :=
  associatorCochain x y z

/-- The additive associator defect on the standard basis vectors. -/
def splitAdditiveAssociatorCoef (x y z : Grade) : ℚ :=
  cochainF x y * cochainF (gradeAdd x y) z -
  cochainF y z * cochainF x (gradeAdd y z)

/-- 
Multiplicative version: `(e_x e_y) e_z = \phi(x,y,z) e_x (e_y e_z)`.
Instead of defining the full algebra product over `Grade`, we verify the cocycle relation
directly on the cochain coefficients.
-/
theorem basis_mul_mul_eq_cocycle_smul (x y z : Grade) :
    cochainF x y * cochainF (gradeAdd x y) z =
    splitAssociativityCocycle x y z * (cochainF y z * cochainF x (gradeAdd y z)) := by
  unfold splitAssociativityCocycle associatorCochain
  have hz : cochainF y z * cochainF x (gradeAdd y z) ≠ 0 := by
    apply mul_ne_zero
    · exact cochainF_ne_zero y z
    · exact cochainF_ne_zero x (gradeAdd y z)
  rw [div_mul_cancel₀ _ hz]

/--
The additive `Ring.associator` defect corresponds exactly to the `splitAdditiveAssociatorCoef`.
Since `[e_x, e_y, e_z] = (e_x e_y) e_z - e_x (e_y e_z)`, the coefficient at `x ⊕ y ⊕ z` is exactly this difference.
-/
theorem basis_associator_eq_cochain_defect (x y z : Grade) :
    (fun b => ((splitOctonionMul 
        (splitOctonionMul (splitBasisVector (basisOfGrade x)) (splitBasisVector (basisOfGrade y)))
        (splitBasisVector (basisOfGrade z))) b : ℚ) -
      ((splitOctonionMul 
        (splitBasisVector (basisOfGrade x))
        (splitOctonionMul (splitBasisVector (basisOfGrade y)) (splitBasisVector (basisOfGrade z)))) b : ℚ)) =
    splitAdditiveAssociatorCoef x y z •
      (fun b => (splitBasisVector (basisOfGrade (gradeAdd (gradeAdd x y) z)) b : ℚ)) := by
  revert x y z
  native_decide

/-- The braiding / exchange sign derived from `cochainF`. -/
def splitBraidingSign (x y : Grade) : ℚ :=
  exchangeCochain x y

/-- 
The exchange relation `e_x e_y = R(x,y) e_y e_x`.
-/
theorem basis_mul_eq_braidingSign_smul_mul (x y : Grade) :
    cochainF x y = splitBraidingSign x y * cochainF y x := by
  exact native_exchange_is_cochain x y

end InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge
"""

with open('lean/InfoGeometry/Canonical/SplitOctonionZ2ThreeCochainBridge.lean', 'w') as f:
    f.write(content)

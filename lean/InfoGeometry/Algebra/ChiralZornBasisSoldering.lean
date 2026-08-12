import Mathlib
import InfoGeometry.Algebra.ZornMatrix

/-!
# Chiral soldering for the split-Zorn basis

This file records the concrete change of basis between the diagonal/off-diagonal
Zorn coordinates and the chiral symbols
`u±, σ±₁, σ±₂, σ±₃`.  It deliberately proves coordinate identities only; no
claim of a new associative or `SU(3)` structure is made here.
-/

namespace InfoGeometry.Algebra

open ZornMatrix

abbrev SplitZornC := ZornMatrix ℂ

abbrev chiralUPlus : SplitZornC := E11
abbrev chiralUMinus : SplitZornC := E22
abbrev chiralSigmaPlus (i : Fin 3) : SplitZornC := U i
abbrev chiralSigmaMinus (i : Fin 3) : SplitZornC := V i

abbrev chiralOne : SplitZornC := I

/-! The hyperbolic diagonal element `ℓ`, with `ℓ² = 1`. -/
def chiralL : SplitZornC where
  a := 1
  v := ![0, 0, 0]
  w := ![0, 0, 0]
  b := -1

@[simp] theorem chiralUPlus_eq_E11 : chiralUPlus = (E11 : SplitZornC) := rfl
@[simp] theorem chiralUMinus_eq_E22 : chiralUMinus = (E22 : SplitZornC) := rfl
@[simp] theorem chiralSigmaPlus_eq_U (i : Fin 3) : chiralSigmaPlus i = U i := rfl
@[simp] theorem chiralSigmaMinus_eq_V (i : Fin 3) : chiralSigmaMinus i = V i := rfl

theorem chiral_diagonal_soldering :
    chiralUPlus + chiralUMinus = chiralOne := by
  dsimp [chiralUPlus, chiralUMinus, chiralOne]
  apply ZornMatrix.ext
  · change (1 + 0 : ℂ) = 1
    ring
  · funext j
    change (ZornMatrix.add E11 E22).v j = (I : SplitZornC).v j
    fin_cases j <;> simp [ZornMatrix.add, Vec3.add, I, E11, E22]
  · funext j
    change (ZornMatrix.add E11 E22).w j = (I : SplitZornC).w j
    fin_cases j <;> simp [ZornMatrix.add, Vec3.add, I, E11, E22]
  · change (0 + 1 : ℂ) = 1
    ring

theorem chiralL_sq : chiralL * chiralL = chiralOne := by
  dsimp [chiralOne]
  apply ZornMatrix.ext
  · change (ZornMatrix.mul chiralL chiralL).a = chiralOne.a
    simp [chiralL, chiralOne, ZornMatrix.mul, Vec3.dot, I]
  · funext j
    change (ZornMatrix.mul chiralL chiralL).v j = (chiralOne : SplitZornC).v j
    fin_cases j <;> simp [chiralL, chiralOne, ZornMatrix.mul,
      Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, Vec3.dot, I]
  · funext j
    change (ZornMatrix.mul chiralL chiralL).w j = (chiralOne : SplitZornC).w j
    fin_cases j <;> simp [chiralL, chiralOne, ZornMatrix.mul,
      Vec3.add, Vec3.sub, Vec3.smul, Vec3.cross, Vec3.dot, I]
  · change (ZornMatrix.mul chiralL chiralL).b = chiralOne.b
    simp [chiralL, chiralOne, ZornMatrix.instMul, ZornMatrix.mul, Vec3.dot, I]

theorem chiralUPlus_reconstruction :
    chiralUPlus = (1 / 2 : ℂ) • (chiralOne + chiralL) := by
  dsimp [chiralUPlus, chiralOne]
  apply ZornMatrix.ext
  · change (1 : ℂ) = (1 / 2 : ℂ) * (1 + 1)
    norm_num
  · funext j
    change chiralUPlus.v j =
      (ZornMatrix.smul (1 / 2 : ℂ) (ZornMatrix.add (chiralOne) chiralL)).v j
    fin_cases j <;> simp [chiralUPlus, chiralOne, chiralL,
      ZornMatrix.smul,
      ZornMatrix.add, Vec3.add, Vec3.smul, I, E11]
  · funext j
    change chiralUPlus.w j =
      (ZornMatrix.smul (1 / 2 : ℂ) (ZornMatrix.add (chiralOne) chiralL)).w j
    fin_cases j <;> simp [chiralUPlus, chiralOne, chiralL,
      ZornMatrix.smul,
      ZornMatrix.add, Vec3.add, Vec3.smul, I, E11]
  · change (0 : ℂ) = (1 / 2 : ℂ) * (1 + (-1))
    norm_num

theorem chiralUMinus_reconstruction :
    chiralUMinus = (1 / 2 : ℂ) • (chiralOne - chiralL) := by
  dsimp [chiralUMinus, chiralOne]
  apply ZornMatrix.ext
  · change (0 : ℂ) = (1 / 2 : ℂ) * (1 - 1)
    norm_num
  · funext j
    change chiralUMinus.v j =
      (ZornMatrix.smul (1 / 2 : ℂ) (ZornMatrix.sub (chiralOne) chiralL)).v j
    fin_cases j <;> simp [chiralUMinus, chiralOne, chiralL,
      ZornMatrix.smul,
      ZornMatrix.sub, Vec3.sub, Vec3.smul, I, E22]
  · funext j
    change chiralUMinus.w j =
      (ZornMatrix.smul (1 / 2 : ℂ) (ZornMatrix.sub (chiralOne) chiralL)).w j
    fin_cases j <;> simp [chiralUMinus, chiralOne, chiralL,
      ZornMatrix.smul,
      ZornMatrix.sub, Vec3.sub, Vec3.smul, I, E22]
  · change (1 : ℂ) = (1 / 2 : ℂ) * (1 - (-1))
    norm_num

theorem chiralL_difference :
    chiralL = chiralUPlus - chiralUMinus := by
  dsimp [chiralL, chiralUPlus, chiralUMinus]
  apply ZornMatrix.ext
  · change (1 : ℂ) = 1 - 0
    ring
  · funext j
    change (chiralL.v) j = (ZornMatrix.sub E11 E22).v j
    fin_cases j <;> simp [chiralL, ZornMatrix.sub, Vec3.sub, E11, E22]
  · funext j
    change (chiralL.w) j = (ZornMatrix.sub E11 E22).w j
    fin_cases j <;> simp [chiralL, ZornMatrix.sub, Vec3.sub, E11, E22]
  · change (-1 : ℂ) = 0 - 1
    ring

def chiralBasis : Fin 8 → SplitZornC
  | 0 => chiralUPlus
  | 1 => chiralSigmaPlus 0
  | 2 => chiralSigmaPlus 1
  | 3 => chiralSigmaPlus 2
  | 4 => chiralUMinus
  | 5 => chiralSigmaMinus 0
  | 6 => chiralSigmaMinus 1
  | 7 => chiralSigmaMinus 2

/-! The reordered Zorn table `(1, ℓ), (i, ℓi), (j, ℓj), (k, ℓk)`.
Here the pairs are represented by the diagonal unit/hyperbolic element and
the three upper/lower off-diagonal coordinate pairs. -/
def solderedBasis : Fin 8 → SplitZornC
  | 0 => chiralOne
  | 1 => chiralL
  | 2 => chiralSigmaPlus 0
  | 3 => chiralSigmaMinus 0
  | 4 => chiralSigmaPlus 1
  | 5 => chiralSigmaMinus 1
  | 6 => chiralSigmaPlus 2
  | 7 => chiralSigmaMinus 2

@[simp] theorem solderedBasis_zero : solderedBasis 0 = chiralOne := rfl
@[simp] theorem solderedBasis_one : solderedBasis 1 = chiralL := rfl
@[simp] theorem solderedBasis_two : solderedBasis 2 = chiralSigmaPlus 0 := rfl
@[simp] theorem solderedBasis_three : solderedBasis 3 = chiralSigmaMinus 0 := rfl
@[simp] theorem solderedBasis_four : solderedBasis 4 = chiralSigmaPlus 1 := rfl
@[simp] theorem solderedBasis_five : solderedBasis 5 = chiralSigmaMinus 1 := rfl
@[simp] theorem solderedBasis_six : solderedBasis 6 = chiralSigmaPlus 2 := rfl
@[simp] theorem solderedBasis_seven : solderedBasis 7 = chiralSigmaMinus 2 := rfl

@[simp] theorem chiralBasis_zero : chiralBasis 0 = chiralUPlus := rfl
@[simp] theorem chiralBasis_one : chiralBasis 1 = chiralSigmaPlus 0 := rfl
@[simp] theorem chiralBasis_two : chiralBasis 2 = chiralSigmaPlus 1 := rfl
@[simp] theorem chiralBasis_three : chiralBasis 3 = chiralSigmaPlus 2 := rfl
@[simp] theorem chiralBasis_four : chiralBasis 4 = chiralUMinus := rfl
@[simp] theorem chiralBasis_five : chiralBasis 5 = chiralSigmaMinus 0 := rfl
@[simp] theorem chiralBasis_six : chiralBasis 6 = chiralSigmaMinus 1 := rfl
@[simp] theorem chiralBasis_seven : chiralBasis 7 = chiralSigmaMinus 2 := rfl

@[simp] theorem chiralSigmaPlus_zero_mul_one :
    chiralSigmaPlus 0 * chiralSigmaPlus 1 = chiralSigmaMinus 2 := by
  exact U_zero_mul_U_one

@[simp] theorem chiralSigmaPlus_one_mul_two :
    chiralSigmaPlus 1 * chiralSigmaPlus 2 = chiralSigmaMinus 0 := by
  exact U_one_mul_U_two

@[simp] theorem chiralSigmaPlus_two_mul_zero :
    chiralSigmaPlus 2 * chiralSigmaPlus 0 = chiralSigmaMinus 1 := by
  exact U_two_mul_U_zero

@[simp] theorem chiralSigmaPlus_same_mul_zero (i : Fin 3) :
    chiralSigmaPlus i * chiralSigmaPlus i = 0 := by
  exact U_mul_self_zero i

@[simp] theorem chiralSigmaMinus_same_mul_zero (i : Fin 3) :
    chiralSigmaMinus i * chiralSigmaMinus i = 0 := by
  exact V_mul_self_zero i

@[simp] theorem chiralSigmaMinus_zero_mul_one :
    chiralSigmaMinus 0 * chiralSigmaMinus 1 = -(chiralSigmaPlus 2) := by
  exact V_zero_mul_V_one

@[simp] theorem chiralSigmaMinus_one_mul_two :
    chiralSigmaMinus 1 * chiralSigmaMinus 2 = -(chiralSigmaPlus 0) := by
  exact V_one_mul_V_two

@[simp] theorem chiralSigmaMinus_two_mul_zero :
    chiralSigmaMinus 2 * chiralSigmaMinus 0 = -(chiralSigmaPlus 1) := by
  exact V_two_mul_V_zero

@[simp] theorem chiralSigmaMinus_one_mul_zero :
    chiralSigmaMinus 1 * chiralSigmaMinus 0 = chiralSigmaPlus 2 := by
  exact V_one_mul_V_zero

@[simp] theorem chiralSigmaMinus_two_mul_one :
    chiralSigmaMinus 2 * chiralSigmaMinus 1 = chiralSigmaPlus 0 := by
  exact V_two_mul_V_one

@[simp] theorem chiralSigmaMinus_zero_mul_two :
    chiralSigmaMinus 0 * chiralSigmaMinus 2 = chiralSigmaPlus 1 := by
  exact V_zero_mul_V_two

@[simp] theorem chiralSigmaPlus_mul_minus (i j : Fin 3) :
    chiralSigmaPlus i * chiralSigmaMinus j =
      if i = j then chiralUPlus else 0 := by
  exact U_mul_V i j

@[simp] theorem chiralSigmaMinus_mul_plus (i j : Fin 3) :
    chiralSigmaMinus i * chiralSigmaPlus j =
      if i = j then chiralUMinus else 0 := by
  exact V_mul_U i j

/-
The chiral Peirce basis reconstructs every split-Zorn element from the two
diagonal idempotents and the three upper/lower chiral coordinate families.
-/
theorem chiralPeirceDecomposition (Z : SplitZornC) :
    Z = Z.a • chiralUPlus + Z.b • chiralUMinus +
        (Z.v 0 • chiralSigmaPlus 0 + Z.v 1 • chiralSigmaPlus 1 +
          Z.v 2 • chiralSigmaPlus 2) +
        (Z.w 0 • chiralSigmaMinus 0 + Z.w 1 • chiralSigmaMinus 1 +
          Z.w 2 • chiralSigmaMinus 2) := by
  have hadd : ∀ X Y : SplitZornC, X + Y = ZornMatrix.add X Y := by
    intro X Y
    rfl
  have hsmul : ∀ (r : ℂ) (X : SplitZornC), r • X = ZornMatrix.smul r X := by
    intro r X
    rfl
  cases Z with
  | mk a v w b =>
      apply ZornMatrix.ext
      · simp [hadd, hsmul, chiralUPlus,
          chiralUMinus, chiralSigmaPlus, chiralSigmaMinus, E11, E22, U, V,
          Vec3.basis, ZornMatrix.smul, ZornMatrix.add, Vec3.add, Vec3.smul]
      · funext i
        fin_cases i <;>
          simp [hadd, hsmul, chiralUPlus,
            chiralUMinus, chiralSigmaPlus, chiralSigmaMinus, E11, E22, U, V,
            Vec3.basis, ZornMatrix.smul, ZornMatrix.add, Vec3.add, Vec3.smul] <;>
          ring
      · funext i
        fin_cases i <;>
          simp [hadd, hsmul, chiralUPlus,
            chiralUMinus, chiralSigmaPlus, chiralSigmaMinus, E11, E22, U, V,
            Vec3.basis, ZornMatrix.smul, ZornMatrix.add, Vec3.add, Vec3.smul] <;>
          ring
      · simp [hadd, hsmul, chiralUPlus,
          chiralUMinus, chiralSigmaPlus, chiralSigmaMinus, E11, E22, U, V,
          Vec3.basis, ZornMatrix.smul, ZornMatrix.add, Vec3.add, Vec3.smul]

end InfoGeometry.Algebra

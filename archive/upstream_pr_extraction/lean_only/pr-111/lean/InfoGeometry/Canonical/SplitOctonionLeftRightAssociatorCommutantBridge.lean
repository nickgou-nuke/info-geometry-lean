import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Left-Right Associator Commutant Bridge

This module formalizes the exact algebraic relationship between the commutator of
Left and Right regular multiplications and the Malcev / nonassociative associator:
$$[x, y, z] = (x \cdot y) \cdot z - x \cdot (y \cdot z).$$

## Key Theorems:
1. **Commutator-Associator Identity**:
   $$[L_x, R_z](y) = L_x(R_z(y)) - R_z(L_x(y)) = x(yz) - (xy)z = -[x, y, z].$$
2. **Commutant Defect Characterization**:
   $$[L_x, R_z] = 0 \iff \forall y, [x, y, z] = 0.$$
3. **Associative Product Specialization**:
   In any associative algebra / subalgebra (e.g. split-quaternions $\mathbb{H}_s$),
   $[L_x, R_z] = 0$ holds identically.
4. **Malcev / $G_2$ Derivations**:
   The canonical derivation $D_{x, z} = [L_x, L_z] + [L_x, R_z] + [R_x, R_z]$ is well-defined
   as an endomorphism of the underlying linear carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionLeftRightAssociatorCommutantBridge

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- A bilinear non-associative multiplication on a real vector space. -/
structure NonAssocProduct (A : Type*) [AddCommGroup A] [Module ℝ A] where
  mul : A → A → A
  add_mul : ∀ x y z, mul (x + y) z = mul x z + mul y z
  mul_add : ∀ x y z, mul x (y + z) = mul x y + mul x z
  smul_mul : ∀ (c : ℝ) x y, mul (c • x) y = c • mul x y
  mul_smul : ∀ (c : ℝ) x y, mul x (c • y) = c • mul x y

variable (P : NonAssocProduct A)

/-- The algebraic associator of three elements:
    $[x, y, z] = (x \cdot y) \cdot z - x \cdot (y \cdot z)$. -/
def associator (x y z : A) : A :=
  P.mul (P.mul x y) z - P.mul x (P.mul y z)

/-- Left regular multiplication operator $L_x : y \mapsto x \cdot y$. -/
def leftMul (x : A) : Module.End ℝ A where
  toFun y := P.mul x y
  map_add' y1 y2 := P.mul_add x y1 y2
  map_smul' c y := by
    dsimp
    rw [P.mul_smul]

/-- Right regular multiplication operator $R_z : y \mapsto y \cdot z$. -/
def rightMul (z : A) : Module.End ℝ A where
  toFun y := P.mul y z
  map_add' y1 y2 := P.add_mul y1 y2 z
  map_smul' c y := by
    dsimp
    rw [P.smul_mul]

@[simp] theorem leftMul_apply (x y : A) : leftMul P x y = P.mul x y := rfl
@[simp] theorem rightMul_apply (z y : A) : rightMul P z y = P.mul y z := rfl

/-- The commutator $[L_x, R_z] = L_x \circ R_z - R_z \circ L_x$ as an endomorphism. -/
def leftRightCommutator (x z : A) : Module.End ℝ A :=
  leftMul P x * rightMul P z - rightMul P z * leftMul P x

/-- 🏆 THEOREM: The Left-Right regular commutator evaluates to the negative associator:
    $[L_x, R_z](y) = -[x, y, z]$. -/
theorem leftRight_commutator_apply_eq_neg_associator (x y z : A) :
    leftRightCommutator P x z y = -associator P x y z := by
  dsimp [leftRightCommutator, associator, leftMul, rightMul]
  abel

/-- 🏆 THEOREM: $[L_x, R_z](y) + [x, y, z] = 0$. -/
theorem leftRight_commutator_add_associator_eq_zero (x y z : A) :
    leftRightCommutator P x z y + associator P x y z = 0 := by
  rw [leftRight_commutator_apply_eq_neg_associator]
  abel

/-- 🏆 THEOREM: Left and Right regular multiplications commute if and only if
    the associator vanishes for all middle arguments:
    $[L_x, R_z] = 0 \iff \forall y, [x, y, z] = 0$. -/
theorem leftRight_commute_iff_associator_zero (x z : A) :
    leftMul P x * rightMul P z = rightMul P z * leftMul P x ↔ ∀ y, associator P x y z = 0 := by
  constructor
  · intro hcomm y
    have h_eval : (leftMul P x * rightMul P z - rightMul P z * leftMul P x) y = 0 := by
      rw [hcomm, sub_self]
      rfl
    have h_neg : -associator P x y z = 0 := by
      rw [← leftRight_commutator_apply_eq_neg_associator]
      exact h_eval
    exact neg_eq_zero.mp h_neg
  · intro hassoc
    apply LinearMap.ext
    intro y
    have h_sub : (leftMul P x * rightMul P z - rightMul P z * leftMul P x) y = 0 := by
      change leftRightCommutator P x z y = 0
      rw [leftRight_commutator_apply_eq_neg_associator, hassoc y, neg_zero]
    exact sub_eq_zero.mp h_sub

/-- 🏆 THEOREM: In an associative product, Left and Right regular representations always commute. -/
theorem leftRight_commute_of_associative (hassoc : ∀ u v w : A, P.mul (P.mul u v) w = P.mul u (P.mul v w))
    (x z : A) :
    leftMul P x * rightMul P z = rightMul P z * leftMul P x := by
  rw [leftRight_commute_iff_associator_zero]
  intro y
  dsimp [associator]
  rw [hassoc, sub_self]

/-- Standard Malcev / $G_2$ derivation operator constructed from left/right commutators:
    $D_{x, z} = [L_x, L_z] + [L_x, R_z] + [R_x, R_z]$. -/
def standardDerivation (x z : A) : Module.End ℝ A :=
  (leftMul P x * leftMul P z - leftMul P z * leftMul P x) +
  (leftMul P x * rightMul P z - rightMul P z * leftMul P x) +
  (rightMul P x * rightMul P z - rightMul P z * rightMul P x)

end InfoGeometry.Canonical.SplitOctonionLeftRightAssociatorCommutantBridge

import Mathlib.Tactic
import InfoGeometry.Physics.MD006OperatorEigenoperators

/-!
# Repaired MD 008: finite representation charge lattice

Source: `github-nick:nickgou-nuke/MD`, file `008.md`.

Chapter 8 applies representation-theory language to the finite operator algebra
from Chapter 6.  The theorem-safe content extracted here is the finite
`A₁ ⊕ A₁` root/weight parity shadow:

* the two Cartan readouts are the left/right `σ₃` eigenvalues already proved
  for the matrix units;
* the four formal roots are `(±2,0)` and `(0,±2)`;
* the root lattice consists of even shifts in each coordinate;
* quotienting integer weights by root-lattice shifts is exactly parity in each
  coordinate, represented by four classes `(0,0)`, `(1,0)`, `(0,1)`, `(1,1)`.

No theorem here asserts the full abstract Lie algebra isomorphism,
Killing-form normalization, Weyl representation classification, boson/fermion
physics, Standard Model charges, or Lorentz-spinoriality classification.  Those
are recorded in the source as interpretation/standard theory and are kept out
of this finite owner.
-/

noncomputable section

namespace InfoGeometry.Physics.MD008RepresentationCharge

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open InfoGeometry.Physics.MD006OperatorEigenoperators
open InfoGeometry.Physics.MD001MatrixQuantumGeometry

/-- Integer two-coordinate weight shadow for `sl₂_L ⊕ sl₂_R`. -/
abbrev Weight := ℤ × ℤ

/-- Formal charge quotient representative: parity in both coordinates. -/
def charge (w : Weight) : Weight :=
  (w.1 % 2, w.2 % 2)

/-- Addition of weight pairs. -/
def addWeight (u v : Weight) : Weight :=
  (u.1 + v.1, u.2 + v.2)

/-- A root-lattice shift: even in each coordinate. -/
def rootShift (a b : ℤ) : Weight :=
  (2 * a, 2 * b)

/-- Positive left `A₁` root. -/
def alphaLPlus : Weight := (2, 0)

/-- Negative left `A₁` root. -/
def alphaLMinus : Weight := (-2, 0)

/-- Positive right `A₁` root. -/
def alphaRPlus : Weight := (0, 2)

/-- Negative right `A₁` root. -/
def alphaRMinus : Weight := (0, -2)

/-- The finite root predicate for `A₁ ⊕ A₁`. -/
def IsA1SumA1Root (w : Weight) : Prop :=
  w = alphaLPlus ∨ w = alphaLMinus ∨ w = alphaRPlus ∨ w = alphaRMinus

/-- Roots lie in the zero charge class because they are root-lattice shifts. -/
theorem charge_root_zero (w : Weight) (hw : IsA1SumA1Root w) :
    charge w = (0, 0) := by
  rcases hw with rfl | rfl | rfl | rfl <;> simp [charge, alphaLPlus, alphaLMinus, alphaRPlus, alphaRMinus]

/-- Adding a root-lattice shift does not change charge. -/
theorem charge_add_rootShift (w : Weight) (a b : ℤ) :
    charge (addWeight w (rootShift a b)) = charge w := by
  ext <;> simp [charge, addWeight, rootShift] <;> omega

/-- The first charge coordinate is always `0` or `1`. -/
theorem charge_first_zero_or_one (w : Weight) :
    (charge w).1 = 0 ∨ (charge w).1 = 1 := by
  simp [charge]
  omega

/-- The second charge coordinate is always `0` or `1`. -/
theorem charge_second_zero_or_one (w : Weight) :
    (charge w).2 = 0 ∨ (charge w).2 = 1 := by
  simp [charge]
  omega

/-- The quotient shadow has exactly the four parity representatives. -/
theorem charge_four_representatives (w : Weight) :
    charge w = (0, 0) ∨ charge w = (1, 0) ∨
      charge w = (0, 1) ∨ charge w = (1, 1) := by
  have h1 := charge_first_zero_or_one w
  have h2 := charge_second_zero_or_one w
  rcases h1 with h10 | h11 <;> rcases h2 with h20 | h21
  · left; ext <;> simp [h10, h20]
  · right; right; left; ext <;> simp [h10, h21]
  · right; left; ext <;> simp [h11, h20]
  · right; right; right; ext <;> simp [h11, h21]

/-- Matrix-unit weight shadow: `E₁₁` has left/right `σ₃` weights `(1,1)`. -/
def weightE11 : Weight := (1, 1)

/-- Matrix-unit weight shadow: `E₁₂` has left/right `σ₃` weights `(1,-1)`. -/
def weightE12 : Weight := (1, -1)

/-- Matrix-unit weight shadow: `E₂₁` has left/right `σ₃` weights `(-1,1)`. -/
def weightE21 : Weight := (-1, 1)

/-- Matrix-unit weight shadow: `E₂₂` has left/right `σ₃` weights `(-1,-1)`. -/
def weightE22 : Weight := (-1, -1)

/-- The already-proved matrix-unit eigenvalues are the four finite Cartan weights. -/
theorem matrix_unit_cartan_weight_packet :
    leftMul UnifiedMatrixBasis.σ₃ E11 = E11 ∧
    rightMul UnifiedMatrixBasis.σ₃ E11 = E11 ∧
    leftMul UnifiedMatrixBasis.σ₃ E12 = E12 ∧
    rightMul UnifiedMatrixBasis.σ₃ E12 = -E12 ∧
    leftMul UnifiedMatrixBasis.σ₃ E21 = -E21 ∧
    rightMul UnifiedMatrixBasis.σ₃ E21 = E21 ∧
    leftMul UnifiedMatrixBasis.σ₃ E22 = -E22 ∧
    rightMul UnifiedMatrixBasis.σ₃ E22 = -E22 := by
  exact ⟨sigma3_E11_joint_eigen.1, sigma3_E11_joint_eigen.2,
    sigma3_E12_joint_eigen.1, sigma3_E12_joint_eigen.2,
    sigma3_E21_joint_eigen.1, sigma3_E21_joint_eigen.2,
    sigma3_E22_joint_eigen.1, sigma3_E22_joint_eigen.2⟩

/-- All four `M₂(ℂ)` matrix-unit weights are odd/odd in the finite parity quotient. -/
theorem matrix_unit_weight_charges :
    charge weightE11 = (1, 1) ∧ charge weightE12 = (1, 1) ∧
    charge weightE21 = (1, 1) ∧ charge weightE22 = (1, 1) := by
  simp [charge, weightE11, weightE12, weightE21, weightE22]

/-- Repaired theorem-safe Chapter 8 finite representation-charge packet. -/
theorem repaired_MD008_representation_charge_packet (w : Weight) (a b : ℤ) :
    charge alphaLPlus = (0, 0) ∧
    charge alphaRPlus = (0, 0) ∧
    charge (addWeight w (rootShift a b)) = charge w ∧
    (charge w = (0, 0) ∨ charge w = (1, 0) ∨
      charge w = (0, 1) ∨ charge w = (1, 1)) ∧
    charge weightE12 = (1, 1) ∧
    leftMul UnifiedMatrixBasis.σ₃ E12 = E12 ∧
    rightMul UnifiedMatrixBasis.σ₃ E12 = -E12 := by
  exact ⟨by simp [charge, alphaLPlus],
    by simp [charge, alphaRPlus],
    charge_add_rootShift w a b,
    charge_four_representatives w,
    matrix_unit_weight_charges.2.1,
    sigma3_E12_joint_eigen.1,
    sigma3_E12_joint_eigen.2⟩

end InfoGeometry.Physics.MD008RepresentationCharge

end noncomputable section

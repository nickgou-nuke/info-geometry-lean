import InfoGeometry.Canonical.OperatorZornDiracRepresentation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Faithful associative operator-Zorn envelope

The repository's associative `OperatorZornMatrix A` is transported from the
ordinary matrix algebra `Matrix (Fin 2) (Fin 2) A`.  This file exposes that
matrix algebra as a reusable envelope even when the coefficient algebra has no
chosen star operation.

It also records the diagonal functor and the faithful left-regular
representation of an associative algebra.  These are the two ingredients
needed to place independently graded algebras in one operator-Zorn-shaped
associative carrier without identifying their underlying products.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope

open scoped Matrix

/-- The faithful associative `2 x 2` envelope of a coefficient ring. -/
abbrev Envelope (A : Type*) [Ring A] := Matrix (Fin 2) (Fin 2) A

variable {A : Type*} [Ring A]

/-- Diagonal embedding into both Zorn sheets. -/
def diagonal (a : A) : Envelope A :=
  !![a, 0; 0, a]

/-- Strict upper Peirce corner. -/
def upper (a : A) : Envelope A :=
  !![0, a; 0, 0]

/-- Strict lower Peirce corner. -/
def lower (a : A) : Envelope A :=
  !![0, 0; a, 0]

/-- Matrix commutator in the associative envelope. -/
def commutator (X Y : Envelope A) : Envelope A :=
  X * Y - Y * X

@[simp] theorem diagonal_apply_zero_zero (a : A) :
    diagonal a 0 0 = a := rfl

@[simp] theorem diagonal_apply_one_one (a : A) :
    diagonal a 1 1 = a := rfl

@[simp] theorem diagonal_zero :
    diagonal (0 : A) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem diagonal_one :
    diagonal (1 : A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem diagonal_add (a b : A) :
    diagonal (a + b) = diagonal a + diagonal b := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem diagonal_neg (a : A) :
    diagonal (-a) = -diagonal a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem diagonal_sub (a b : A) :
    diagonal (a - b) = diagonal a - diagonal b := by
  rw [sub_eq_add_neg, diagonal_add, diagonal_neg]

@[simp] theorem diagonal_mul (a b : A) :
    diagonal (a * b) = diagonal a * diagonal b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The diagonal embedding is a native ring homomorphism. -/
def diagonalRingHom : A →+* Envelope A where
  toFun := diagonal
  map_one' := diagonal_one
  map_mul' := diagonal_mul
  map_zero' := diagonal_zero
  map_add' := diagonal_add

/-- The diagonal embedding is faithful. -/
theorem diagonal_injective :
    Function.Injective (diagonal : A → Envelope A) := by
  intro a b hab
  exact congrArg (fun M : Envelope A => M 0 0) hab

@[simp] theorem diagonal_commutator (a b : A) :
    commutator (diagonal a) (diagonal b) =
      diagonal (a * b - b * a) := by
  rw [commutator, ← diagonal_mul, ← diagonal_mul, ← diagonal_sub]

@[simp] theorem upper_sq_zero (a : A) :
    upper a * upper a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem lower_sq_zero (a : A) :
    lower a * lower a = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, Matrix.mul_apply, Fin.sum_univ_two]

section Algebra

variable [Algebra ℝ A]

@[simp] theorem diagonal_smul (r : ℝ) (a : A) :
    diagonal (r • a) = r • diagonal a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Diagonal embedding as an algebra homomorphism. -/
def diagonalAlgHom : A →ₐ[ℝ] Envelope A where
  toFun := diagonal
  map_one' := diagonal_one
  map_mul' := diagonal_mul
  map_zero' := diagonal_zero
  map_add' := diagonal_add
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal]

/-- Adjoint grade in the represented envelope. -/
def HasAdjointGrade (H : A) (k : ℤ) (X : Envelope A) : Prop :=
  commutator (diagonal H) X = (k : ℝ) • X

/-- A homogeneous coefficient remains homogeneous after diagonal embedding. -/
theorem diagonal_preserves_adjoint_grade
    (H x : A) (k : ℤ)
    (hx : H * x - x * H = (k : ℝ) • x) :
    HasAdjointGrade H k (diagonal x) := by
  unfold HasAdjointGrade
  rw [diagonal_commutator, hx, diagonal_smul]

/-- Left multiplication as a linear endomorphism. -/
def leftMultiply (a : A) : Module.End ℝ A where
  toFun x := a * x
  map_add' x y := by rw [mul_add]
  map_smul' r x := by
    exact (Algebra.mul_smul_comm r a x).symm

@[simp] theorem leftMultiply_apply (a x : A) :
    leftMultiply a x = a * x := rfl

@[simp] theorem leftMultiply_one (a : A) :
    leftMultiply a 1 = a := by simp

@[simp] theorem leftMultiply_mul (a b : A) :
    leftMultiply (a * b) = leftMultiply a * leftMultiply b := by
  apply LinearMap.ext
  intro x
  simp [leftMultiply, mul_assoc]

@[simp] theorem leftMultiply_add (a b : A) :
    leftMultiply (a + b) = leftMultiply a + leftMultiply b := by
  apply LinearMap.ext
  intro x
  simp [leftMultiply, add_mul]

@[simp] theorem leftMultiply_smul (r : ℝ) (a : A) :
    leftMultiply (r • a) = r • leftMultiply a := by
  apply LinearMap.ext
  intro x
  simp [leftMultiply, Algebra.smul_mul_assoc]

/-- Faithful left-regular algebra representation. -/
def leftRegularRepresentation : A →ₐ[ℝ] Module.End ℝ A where
  toFun := leftMultiply
  map_one' := by
    apply LinearMap.ext
    intro x
    simp [leftMultiply]
  map_mul' := leftMultiply_mul
  map_zero' := by
    apply LinearMap.ext
    intro x
    simp [leftMultiply]
  map_add' := leftMultiply_add
  commutes' r := by
    apply LinearMap.ext
    intro x
    simp [leftMultiply, Algebra.smul_mul_assoc]

/-- Faithfulness follows by evaluating a left multiplier at the unit. -/
theorem leftRegularRepresentation_injective :
    Function.Injective (leftRegularRepresentation :
      A →ₐ[ℝ] Module.End ℝ A) := by
  intro a b hab
  have h1 := congrArg (fun T : Module.End ℝ A => T 1) hab
  simpa using h1

/-- Left regular representation sends source commutators to operator
commutators. -/
theorem leftRegular_commutator (a b : A) :
    leftMultiply (a * b - b * a) =
      leftMultiply a * leftMultiply b -
        leftMultiply b * leftMultiply a := by
  rw [sub_eq_add_neg, leftMultiply_add]
  apply LinearMap.ext
  intro x
  simp [leftMultiply, mul_assoc]

/-- Source adjoint degree is preserved by the faithful regular action. -/
theorem leftRegular_preserves_adjoint_grade
    (H x : A) (k : ℤ)
    (hx : H * x - x * H = (k : ℝ) • x) :
    leftMultiply H * leftMultiply x - leftMultiply x * leftMultiply H =
      (k : ℝ) • leftMultiply x := by
  rw [← leftRegular_commutator, hx, leftMultiply_smul]

end Algebra

section ExistingOperatorZorn

variable [StarRing A]

/-- Existing associative operator-Zorn carrier represented in this envelope. -/
def existingOperatorZornRepresentation :
    InfoGeometry.Physics.OperatorZornMatrix A →+* Envelope A :=
  InfoGeometry.Canonical.OperatorZornDiracRepresentation.zornDiracRepresentation A

/-- The existing transported operator-Zorn representation is faithful. -/
theorem existingOperatorZornRepresentation_injective :
    Function.Injective
      (existingOperatorZornRepresentation (A := A)) :=
  InfoGeometry.Canonical.OperatorZornDiracRepresentation.
    zornDiracRepresentation_injective

end ExistingOperatorZorn

end InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope

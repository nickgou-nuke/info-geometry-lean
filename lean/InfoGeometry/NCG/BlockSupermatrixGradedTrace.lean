import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix

namespace InfoGeometry.NCG.BlockSupermatrixGradedTrace

/-- The two parities of a Z2-graded object. -/
inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace Parity

/-- Addition of parities modulo two. -/
def add : Parity → Parity → Parity
  | .even, p => p
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : Add Parity := ⟨add⟩

@[simp] theorem even_add (p : Parity) : Parity.even + p = p := rfl
@[simp] theorem odd_add_even : Parity.odd + Parity.even = Parity.odd := rfl
@[simp] theorem odd_add_odd : Parity.odd + Parity.odd = Parity.even := rfl

/-- Koszul sign `(-1)^(|x||y|)`. -/
def sign (R : Type*) [Ring R] : Parity → Parity → R
  | .odd, .odd => -1
  | _, _ => 1

end Parity

variable {m n R : Type*}
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [CommRing R]

/--
A finite `(m|n)` block supermatrix.  Parity is represented by block support:
even homogeneous matrices are block diagonal and odd homogeneous matrices are
off diagonal.

The coefficient ring is ordinary and commutative.  This is the endomorphism
superalgebra grading; it is distinct from a Grassmann grading on coefficients.
-/
structure SuperMatrix where
  A : Matrix m m R
  B : Matrix m n R
  C : Matrix n m R
  D : Matrix n n R

namespace SuperMatrix

@[ext]
theorem ext (X Y : SuperMatrix (m := m) (n := n) (R := R))
    (hA : X.A = Y.A) (hB : X.B = Y.B)
    (hC : X.C = Y.C) (hD : X.D = Y.D) : X = Y := by
  cases X
  cases Y
  simp_all

instance : Zero (SuperMatrix (m := m) (n := n) (R := R)) :=
  ⟨⟨0, 0, 0, 0⟩⟩

instance : Add (SuperMatrix (m := m) (n := n) (R := R)) where
  add X Y := ⟨X.A + Y.A, X.B + Y.B, X.C + Y.C, X.D + Y.D⟩

instance : Neg (SuperMatrix (m := m) (n := n) (R := R)) where
  neg X := ⟨-X.A, -X.B, -X.C, -X.D⟩

instance : Sub (SuperMatrix (m := m) (n := n) (R := R)) where
  sub X Y := ⟨X.A - Y.A, X.B - Y.B, X.C - Y.C, X.D - Y.D⟩

/-- Ordinary block multiplication on the graded endomorphism carrier. -/
def mul (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    SuperMatrix (m := m) (n := n) (R := R) :=
  ⟨X.A * Y.A + X.B * Y.C,
   X.A * Y.B + X.B * Y.D,
   X.C * Y.A + X.D * Y.C,
   X.C * Y.B + X.D * Y.D⟩

instance : Mul (SuperMatrix (m := m) (n := n) (R := R)) := ⟨mul⟩

@[simp] theorem mul_A (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    (X * Y).A = X.A * Y.A + X.B * Y.C := rfl
@[simp] theorem mul_B (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    (X * Y).B = X.A * Y.B + X.B * Y.D := rfl
@[simp] theorem mul_C (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    (X * Y).C = X.C * Y.A + X.D * Y.C := rfl
@[simp] theorem mul_D (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    (X * Y).D = X.C * Y.B + X.D * Y.D := rfl

/-- Supertrace `str X = Tr A - Tr D`. -/
def supertrace (X : SuperMatrix (m := m) (n := n) (R := R)) : R :=
  Matrix.trace X.A - Matrix.trace X.D

/-- Homogeneous block-support predicate. -/
def IsHomogeneous (p : Parity)
    (X : SuperMatrix (m := m) (n := n) (R := R)) : Prop :=
  match p with
  | .even => X.B = 0 ∧ X.C = 0
  | .odd => X.A = 0 ∧ X.D = 0

/-- The graded commutator on homogeneous parity tags. -/
def superbracket (pX pY : Parity)
    (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    SuperMatrix (m := m) (n := n) (R := R) :=
  match pX, pY with
  | .odd, .odd => X * Y + Y * X
  | _, _ => X * Y - Y * X

@[simp] theorem supertrace_zero :
    supertrace (0 : SuperMatrix (m := m) (n := n) (R := R)) = 0 := by
  change Matrix.trace (0 : Matrix m m R) - Matrix.trace (0 : Matrix n n R) = 0
  simp

 theorem supertrace_add
    (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    supertrace (X + Y) = supertrace X + supertrace Y := by
  change Matrix.trace (X.A + Y.A) - Matrix.trace (X.D + Y.D) = _
  rw [Matrix.trace_add, Matrix.trace_add]
  simp only [supertrace]
  ring

 theorem supertrace_sub
    (X Y : SuperMatrix (m := m) (n := n) (R := R)) :
    supertrace (X - Y) = supertrace X - supertrace Y := by
  change Matrix.trace (X.A - Y.A) - Matrix.trace (X.D - Y.D) = _
  rw [Matrix.trace_sub, Matrix.trace_sub]
  simp only [supertrace]
  ring

/-- Even-even products are cyclic under supertrace. -/
theorem supertrace_mul_even_even
    (X Y : SuperMatrix (m := m) (n := n) (R := R))
    (hX : IsHomogeneous .even X) (hY : IsHomogeneous .even Y) :
    supertrace (X * Y) = supertrace (Y * X) := by
  rcases hX with ⟨hXB, hXC⟩
  rcases hY with ⟨hYB, hYC⟩
  simp [supertrace, hXB, hXC, hYB, hYC]
  rw [Matrix.trace_mul_comm X.A Y.A, Matrix.trace_mul_comm X.D Y.D]

/-- A mixed even-odd product has zero diagonal and hence zero supertrace. -/
theorem supertrace_mul_even_odd
    (X Y : SuperMatrix (m := m) (n := n) (R := R))
    (hX : IsHomogeneous .even X) (hY : IsHomogeneous .odd Y) :
    supertrace (X * Y) = 0 := by
  rcases hX with ⟨hXB, hXC⟩
  rcases hY with ⟨hYA, hYD⟩
  simp [supertrace, hXB, hXC, hYA, hYD]

/-- A mixed odd-even product has zero diagonal and hence zero supertrace. -/
theorem supertrace_mul_odd_even
    (X Y : SuperMatrix (m := m) (n := n) (R := R))
    (hX : IsHomogeneous .odd X) (hY : IsHomogeneous .even Y) :
    supertrace (X * Y) = 0 := by
  rcases hX with ⟨hXA, hXD⟩
  rcases hY with ⟨hYB, hYC⟩
  simp [supertrace, hXA, hXD, hYB, hYC]

/-- Odd-odd products are anticyclic under the supertrace. -/
theorem supertrace_mul_odd_odd
    (X Y : SuperMatrix (m := m) (n := n) (R := R))
    (hX : IsHomogeneous .odd X) (hY : IsHomogeneous .odd Y) :
    supertrace (X * Y) = - supertrace (Y * X) := by
  rcases hX with ⟨hXA, hXD⟩
  rcases hY with ⟨hYA, hYD⟩
  simp [supertrace, hXA, hXD, hYA, hYD]
  rw [Matrix.trace_mul_comm X.B Y.C, Matrix.trace_mul_comm X.C Y.B]

/-- Graded cyclicity `str(XY) = (-1)^(|X||Y|) str(YX)`. -/
theorem supertrace_mul_graded_comm
    (pX pY : Parity)
    (X Y : SuperMatrix (m := m) (n := n) (R := R))
    (hX : IsHomogeneous pX X) (hY : IsHomogeneous pY Y) :
    supertrace (X * Y) = Parity.sign R pX pY * supertrace (Y * X) := by
  cases pX <;> cases pY
  · simpa [Parity.sign] using supertrace_mul_even_even X Y hX hY
  · rw [supertrace_mul_even_odd X Y hX hY,
      supertrace_mul_odd_even Y X hY hX]
    simp [Parity.sign]
  · rw [supertrace_mul_odd_even X Y hX hY,
      supertrace_mul_even_odd Y X hY hX]
    simp [Parity.sign]
  · simpa [Parity.sign] using supertrace_mul_odd_odd X Y hX hY

/-- The supertrace annihilates every homogeneous supercommutator. -/
theorem supertrace_superbracket_eq_zero
    (pX pY : Parity)
    (X Y : SuperMatrix (m := m) (n := n) (R := R))
    (hX : IsHomogeneous pX X) (hY : IsHomogeneous pY Y) :
    supertrace (superbracket pX pY X Y) = 0 := by
  cases pX <;> cases pY
  · simp [superbracket, supertrace_sub,
      supertrace_mul_even_even X Y hX hY]
  · rw [show superbracket .even .odd X Y = X * Y - Y * X by rfl,
      supertrace_sub, supertrace_mul_even_odd X Y hX hY,
      supertrace_mul_odd_even Y X hY hX]
    simp
  · rw [show superbracket .odd .even X Y = X * Y - Y * X by rfl,
      supertrace_sub, supertrace_mul_odd_even X Y hX hY,
      supertrace_mul_even_odd Y X hY hX]
    simp
  · rw [show superbracket .odd .odd X Y = X * Y + Y * X by rfl,
      supertrace_add, supertrace_mul_odd_odd X Y hX hY]
    simp

end SuperMatrix

/-!
The super-Jacobi polynomial identity is independent of the block realization.
It follows in every associative ring once parity tags choose commutator versus
anticommutator.  Homogeneity is needed to interpret the tags as actual degrees,
not for the underlying polynomial cancellation.
-/
section AssociativeSuperJacobi

variable {A : Type*} [Ring A]

/-- Parity-tagged supercommutator in an arbitrary associative ring. -/
def ringSuperbracket (pX pY : Parity) (X Y : A) : A :=
  match pX, pY with
  | .odd, .odd => X * Y + Y * X
  | _, _ => X * Y - Y * X

/-- Graded skew symmetry of the parity-tagged supercommutator. -/
theorem ringSuperbracket_skew (pX pY : Parity) (X Y : A) :
    ringSuperbracket pX pY X Y =
      -(Parity.sign A pX pY * ringSuperbracket pY pX Y X) := by
  cases pX <;> cases pY <;>
    simp [ringSuperbracket, Parity.sign] <;> abel

/-- The cyclic graded super-Jacobi identity in every associative ring. -/
theorem graded_super_jacobi
    (pX pY pZ : Parity) (X Y Z : A) :
    Parity.sign A pX pZ *
        ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
      Parity.sign A pY pX *
        ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
      Parity.sign A pZ pY *
        ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0 := by
  cases pX <;> cases pY <;> cases pZ <;>
    simp [ringSuperbracket, Parity.add, Parity.sign,
      mul_add, add_mul, mul_sub, sub_mul, mul_assoc] <;> abel

/-- The adjoint superbracket is a graded derivation of the bracket. -/
theorem super_adjoint_derivation
    (pX pY pZ : Parity) (X Y Z : A) :
    ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) =
      ringSuperbracket (pX + pY) pZ (ringSuperbracket pX pY X Y) Z +
        Parity.sign A pX pY *
          ringSuperbracket pY (pX + pZ) Y (ringSuperbracket pX pZ X Z) := by
  cases pX <;> cases pY <;> cases pZ <;>
    simp [ringSuperbracket, Parity.add, Parity.sign,
      mul_add, add_mul, mul_sub, sub_mul, mul_assoc] <;> abel

end AssociativeSuperJacobi

end InfoGeometry.NCG.BlockSupermatrixGradedTrace

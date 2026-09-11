import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split Octonions: Zorn Vector Matrix Algebra

This module implements the explicit Zorn vector matrix calculus for split composition algebras,
following Konrad Voelkel's PhD thesis (Chapter 3).

The split octonions $O_R$ over a commutative ring $R$ can be represented as Zorn vector matrices:
$$ x = \begin{pmatrix} x^{11} & x^{21} \\ -x^{22} & x^{12} \end{pmatrix} $$
where $x^{11}, x^{12} \in R$ and $x^{21}, x^{22} \in R^3$ (or generally a module $V$).
The norm is given by $N(x) = x^{11}x^{12} + B(x^{21}, x^{22})$, where $B$ is the dot product.

Here we formalize the fundamental matrix operations and prove Voelkel's Lemma 3.1.13:
Octonions with entries strictly on the diagonal associate with all other entries.
This is the local associativity bridge used by the projective boundary files
without requiring full associativity.
-/

namespace InfoGeometry.Projective.SplitOctonions

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/--
A Zorn vector matrix following Voelkel's Convention 3.1.12.
$x^{11}$ and $x^{12}$ are the diagonal scalar components.
$x^{21}$ and $x^{22}$ are the off-diagonal vector components.
Notice the structural minus sign on $x^{22}$ is absorbed into the definition of the operations.
-/
@[ext]
structure ZornMatrix (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  x11 : R
  x12 : R
  x21 : V
  x22 : V

namespace ZornMatrix

instance : Zero (ZornMatrix R V) where
  zero := { x11 := 0, x12 := 0, x21 := 0, x22 := 0 }

@[simp] theorem zero_x11 : (0 : ZornMatrix R V).x11 = 0 := rfl
@[simp] theorem zero_x12 : (0 : ZornMatrix R V).x12 = 0 := rfl
@[simp] theorem zero_x21 : (0 : ZornMatrix R V).x21 = 0 := rfl
@[simp] theorem zero_x22 : (0 : ZornMatrix R V).x22 = 0 := rfl

variable (B : V →ₗ[R] V →ₗ[R] R)

/-- The split norm form $N(x) = x^{11} x^{12} + x^{21} \cdot x^{22}$. -/
def norm (x : ZornMatrix R V) : R :=
  x.x11 * x.x12 + B x.x21 x.x22

/--
The Zorn matrix non-associative product (Voelkel page 34).
This explicitly omits the cross product, using only the Euclidean scalar product.
The non-associativity arises strictly from the `A (B \cdot C) \neq B (A \cdot C)` mismatch!
-/
def mul (x y : ZornMatrix R V) : ZornMatrix R V where
  x11 := x.x11 * y.x11 - B x.x21 y.x22
  x12 := x.x12 * y.x12 - B x.x22 y.x21
  x21 := (x.x11 • y.x21) + (y.x12 • x.x21)
  x22 := (x.x12 • y.x22) + (y.x11 • x.x22)

/-- The canonical involution $x^*$. -/
def star (x : ZornMatrix R V) : ZornMatrix R V where
  x11 := x.x12
  x12 := x.x11
  x21 := -x.x21
  x22 := -x.x22

/-- An element strictly on the diagonal. -/
def diag (α β : R) : ZornMatrix R V where
  x11 := α
  x12 := β
  x21 := 0
  x22 := 0

/-!
### Voelkel Lemma 3.1.13: Diagonal Associativity
Octonions with entries on the diagonal associate with all other entries.
-/

/-- Voelkel Lemma 3.1.13 (1): `(x * y) * χ = x * (y * χ)` when `χ` is diagonal. -/
theorem diag_assoc_right (x y : ZornMatrix R V) (α β : R) :
    mul B (mul B x y) (diag α β) = mul B x (mul B y (diag α β)) := by
  ext
  · dsimp [mul, diag]
    simp [map_sub, map_smul, smul_eq_mul]
    ring
  · dsimp [mul, diag]
    simp [map_sub, map_smul, smul_eq_mul]
    ring
  · dsimp [mul, diag]
    simp [map_add, map_smul]
    module
  · dsimp [mul, diag]
    simp [map_add, map_smul]
    module

/-- Voelkel Lemma 3.1.13 (2): `(x * χ) * y = x * (χ * y)` when `χ` is diagonal. -/
theorem diag_assoc_mid (x y : ZornMatrix R V) (α β : R) :
    mul B (mul B x (diag α β)) y = mul B x (mul B (diag α β) y) := by
  ext
  · dsimp [mul, diag]
    simp [map_sub, map_smul, smul_eq_mul]
    ring
  · dsimp [mul, diag]
    simp [map_sub, map_smul, smul_eq_mul]
    ring
  · dsimp [mul, diag]
    simp [map_add, map_smul]
    module
  · dsimp [mul, diag]
    simp [map_add, map_smul]
    module

/-- Voelkel Lemma 3.1.13 (3): `(χ * x) * y = χ * (x * y)` when `χ` is diagonal. -/
theorem diag_assoc_left (x y : ZornMatrix R V) (α β : R) :
    mul B (mul B (diag α β) x) y = mul B (diag α β) (mul B x y) := by
  ext
  · dsimp [mul, diag]
    simp [map_sub, map_smul, smul_eq_mul]
    ring
  · dsimp [mul, diag]
    simp [map_sub, map_smul, smul_eq_mul]
    ring
  · dsimp [mul, diag]
    simp [map_add, map_smul]
    module
  · dsimp [mul, diag]
    simp [map_add, map_smul]
    module

end ZornMatrix

end InfoGeometry.Projective.SplitOctonions

import Mathlib.Tactic

/-!
# Dual split-quaternion exact backbone

This module is the Lean twin of `tools/sympy/dual_split_quaternion_backbone.py`.

It records the exact finite algebraic backbone for split quaternions and their
central dual-number extension:

* `i² = -1`, `j² = 1`, `k² = 1`, `(ij)k = 1`;
* split-quaternion multiplication is associative;
* conjugation gives the split norm `a² + b² - c² - d²`;
* the dual extension `(p₁ + εp₂)(q₁ + εq₂) = p₁q₁ + ε(p₁q₂ + p₂q₁)` has
  `ε² = 0` and the expected base/infinitesimal product rules.

The companion verifier also checks the same backbone with SymPy, `clifford`,
`galgebra`, GAP, and Sage.

#### BUCKET 1: CLOSED FINITE THEOREMS

All the declarations below are concrete integer coordinate equalities.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not prove Lorentzian screw-motion classification, an
`SO(2,2) ⋉ R⁴` theorem, `Aut(DH_s)`, or any automorphism-group classification.
The GAP evidence is only the finite signed-unit subgroup of the base split
quaternions; `ε` is not a multiplicative unit because `ε² = 0`.
-/

namespace InfoGeometry.OperatorAlgebra.DualSplitQuaternionBackbone

/-- Integer-coordinate split quaternion `a + b i + c j + d k`. -/
structure SplitQ where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq, Repr

namespace SplitQ

/-- Coordinatewise addition. -/
def add (x y : SplitQ) : SplitQ :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

/-- Coordinatewise negation. -/
def neg (x : SplitQ) : SplitQ :=
  ⟨-x.a, -x.b, -x.c, -x.d⟩

/-- Split-quaternion multiplication with `i²=-1`, `j²=k²=1`, and `ij=k`. -/
def mul (x y : SplitQ) : SplitQ :=
  ⟨x.a * y.a - x.b * y.b + x.c * y.c + x.d * y.d,
    x.a * y.b + x.b * y.a - x.c * y.d + x.d * y.c,
    x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b,
    x.a * y.d + x.b * y.c - x.c * y.b + x.d * y.a⟩

/-- Quaternion conjugation: flip all vector signs. -/
def conj (x : SplitQ) : SplitQ :=
  ⟨x.a, -x.b, -x.c, -x.d⟩

/-- Split norm scalar `a² + b² - c² - d²`. -/
def normScalar (x : SplitQ) : ℤ :=
  x.a * x.a + x.b * x.b - x.c * x.c - x.d * x.d

/-- Zero split quaternion. -/
def zero : SplitQ := ⟨0, 0, 0, 0⟩

/-- Unit split quaternion. -/
def one : SplitQ := ⟨1, 0, 0, 0⟩

/-- Generator with square `-1`. -/
def i : SplitQ := ⟨0, 1, 0, 0⟩

/-- Generator with square `1`. -/
def j : SplitQ := ⟨0, 0, 1, 0⟩

/-- Generator `k = ij`, with square `1`. -/
def k : SplitQ := ⟨0, 0, 0, 1⟩

theorem i_sq : mul i i = neg one := by
  rfl

theorem j_sq : mul j j = one := by
  rfl

theorem k_sq : mul k k = one := by
  rfl

theorem ij_eq_k : mul i j = k := by
  rfl

theorem ji_eq_neg_k : mul j i = neg k := by
  rfl

theorem jk_eq_neg_i : mul j k = neg i := by
  rfl

theorem kj_eq_i : mul k j = i := by
  rfl

theorem ki_eq_j : mul k i = j := by
  rfl

theorem ik_eq_neg_j : mul i k = neg j := by
  rfl

theorem ijk_eq_one : mul (mul i j) k = one := by
  rfl

theorem mul_assoc (x y z : SplitQ) : mul (mul x y) z = mul x (mul y z) := by
  cases x
  cases y
  cases z
  simp [mul]
  ring_nf
  repeat constructor

theorem mul_conj_eq_norm (x : SplitQ) :
    mul x (conj x) = ⟨normScalar x, 0, 0, 0⟩ := by
  cases x
  simp [mul, conj, normScalar]
  ring_nf
  repeat constructor

end SplitQ

/-- Dual split quaternion `primal + ε tangent`. -/
structure DualSplitQ where
  primal : SplitQ
  tangent : SplitQ
  deriving DecidableEq, Repr

namespace DualSplitQ

/-- Zero dual split quaternion. -/
def zero : DualSplitQ := ⟨SplitQ.zero, SplitQ.zero⟩

/-- Base embedding `x ↦ x + ε0`. -/
def baseLift (x : SplitQ) : DualSplitQ := ⟨x, SplitQ.zero⟩

/-- Infinitesimal embedding `x ↦ 0 + εx`. -/
def epsLift (x : SplitQ) : DualSplitQ := ⟨SplitQ.zero, x⟩

/-- The distinguished dual-number generator `ε`. -/
def epsilon : DualSplitQ := epsLift SplitQ.one

/-- Dual-number extension of the split-quaternion product. -/
def mul (x y : DualSplitQ) : DualSplitQ :=
  ⟨SplitQ.mul x.primal y.primal,
    SplitQ.add (SplitQ.mul x.primal y.tangent) (SplitQ.mul x.tangent y.primal)⟩

/-- Conjugation acts on both split-quaternion slots. -/
def conj (x : DualSplitQ) : DualSplitQ :=
  ⟨SplitQ.conj x.primal, SplitQ.conj x.tangent⟩

/-- Coordinate count of the dual split-quaternion bookkeeping surface. -/
def coordinateCount : Nat := 8

theorem coordinate_count : coordinateCount = 8 := by
  rfl

theorem baseLift_mul (x y : SplitQ) :
    mul (baseLift x) (baseLift y) = baseLift (SplitQ.mul x y) := by
  cases x
  cases y
  simp [mul, baseLift, SplitQ.add, SplitQ.mul, SplitQ.zero]

theorem epsLift_mul_epsLift_zero (x y : SplitQ) :
    mul (epsLift x) (epsLift y) = zero := by
  cases x
  cases y
  simp [mul, epsLift, zero, SplitQ.add, SplitQ.mul, SplitQ.zero]

theorem baseLift_mul_epsLift (x y : SplitQ) :
    mul (baseLift x) (epsLift y) = epsLift (SplitQ.mul x y) := by
  cases x
  cases y
  simp [mul, baseLift, epsLift, SplitQ.add, SplitQ.mul, SplitQ.zero]

theorem epsLift_mul_baseLift (x y : SplitQ) :
    mul (epsLift x) (baseLift y) = epsLift (SplitQ.mul x y) := by
  cases x
  cases y
  simp [mul, baseLift, epsLift, SplitQ.add, SplitQ.mul, SplitQ.zero]

theorem epsilon_sq_zero : mul epsilon epsilon = zero := by
  exact epsLift_mul_epsLift_zero SplitQ.one SplitQ.one

theorem epsilon_sq_ne_one : mul epsilon epsilon ≠ baseLift SplitQ.one := by
  intro h
  have hprimal : (mul epsilon epsilon).primal = (baseLift SplitQ.one).primal :=
    congrArg DualSplitQ.primal h
  have h0 : (0 : ℤ) = 1 := by
    simpa [epsilon, epsLift, baseLift, mul, zero, SplitQ.zero, SplitQ.one, SplitQ.mul]
      using congrArg SplitQ.a hprimal
  omega

theorem primal_projection_mul (x y : DualSplitQ) :
    (mul x y).primal = SplitQ.mul x.primal y.primal := by
  rfl

theorem mul_assoc (x y z : DualSplitQ) : mul (mul x y) z = mul x (mul y z) := by
  cases x with
  | mk xp xt =>
  cases y with
  | mk yp yt =>
  cases z with
  | mk zp zt =>
  cases xp
  cases xt
  cases yp
  cases yt
  cases zp
  cases zt
  simp [mul, SplitQ.mul, SplitQ.add]
  ring_nf
  repeat constructor

end DualSplitQ

end InfoGeometry.OperatorAlgebra.DualSplitQuaternionBackbone

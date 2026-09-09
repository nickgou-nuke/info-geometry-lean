import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# InfoGeometry.Clifford.Cl11CoordinateAlgebra

Finite coordinate algebra for the split Clifford seed `Cl(1,1)`.

The repository already has Mathlib-canonical Clifford and matrix surfaces for
`Cl(1,1)` in modules such as `Cl11Quaternion`, `Cl11Matrix`, and the tensor-tower
files.  This module adds a small coordinate model with basis
`1, e₁, e₂, e₁₂`, multiplication table

* `e₁² = 1`,
* `e₂² = -1`,
* `e₁₂ = e₁ * e₂`,
* `e₂ * e₁ = -e₁₂`,
* `e₁₂² = 1`,

and proves the finite inner-commutator derivation identities.

This is finite algebra only.  It does not assert a von Neumann algebra
Connes--Radon--Nikodym theorem, a spectral-triple theorem, or a completed
operator-algebraic modular-flow construction.
-/

namespace InfoGeometry.Clifford.Cl11CoordinateAlgebra

/-- Coordinate model for the real split Clifford algebra `Cl(1,1)`. -/
@[ext]
structure Cl11 where
  /-- Scalar coordinate. -/
  s : ℝ
  /-- Positive generator coordinate. -/
  e1 : ℝ
  /-- Negative generator coordinate. -/
  e2 : ℝ
  /-- Bivector coordinate, with convention `e₁₂ = e₁ * e₂`. -/
  e12 : ℝ

/-- Zero coordinate. -/
def zero : Cl11 :=
  ⟨0, 0, 0, 0⟩

/-- Unit coordinate. -/
def one : Cl11 :=
  ⟨1, 0, 0, 0⟩

/-- Coordinate addition. -/
def add (q₁ q₂ : Cl11) : Cl11 :=
  ⟨q₁.s + q₂.s, q₁.e1 + q₂.e1, q₁.e2 + q₂.e2, q₁.e12 + q₂.e12⟩

/-- Coordinate subtraction. -/
def sub (q₁ q₂ : Cl11) : Cl11 :=
  ⟨q₁.s - q₂.s, q₁.e1 - q₂.e1, q₁.e2 - q₂.e2, q₁.e12 - q₂.e12⟩

/-- Coordinate negation. -/
def neg (q : Cl11) : Cl11 :=
  ⟨-q.s, -q.e1, -q.e2, -q.e12⟩

/-- Coordinate scalar multiplication. -/
def smul (c : ℝ) (q : Cl11) : Cl11 :=
  ⟨c * q.s, c * q.e1, c * q.e2, c * q.e12⟩

/--
Coordinate Clifford product for signature `(1,1)` with convention
`e₁₂ = e₁ * e₂`.
-/
def mul (q₁ q₂ : Cl11) : Cl11 :=
  ⟨q₁.s * q₂.s + q₁.e1 * q₂.e1 - q₁.e2 * q₂.e2 + q₁.e12 * q₂.e12,
    q₁.s * q₂.e1 + q₁.e1 * q₂.s + q₁.e2 * q₂.e12 - q₁.e12 * q₂.e2,
    q₁.s * q₂.e2 + q₁.e2 * q₂.s + q₁.e1 * q₂.e12 - q₁.e12 * q₂.e1,
    q₁.s * q₂.e12 + q₁.e12 * q₂.s + q₁.e1 * q₂.e2 - q₁.e2 * q₂.e1⟩

instance : Zero Cl11 where
  zero := zero

instance : One Cl11 where
  one := one

instance : Add Cl11 where
  add := add

instance : Sub Cl11 where
  sub := sub

instance : Neg Cl11 where
  neg := neg

instance : SMul ℝ Cl11 where
  smul := smul

/-- Coordinate-wise natural scalar multiplication. -/
def nsmul : ℕ → Cl11 → Cl11
  | 0, _ => 0
  | Nat.succ n, q => nsmul n q + q

/-- Coordinate-wise integer scalar multiplication. -/
def zsmul : ℤ → Cl11 → Cl11
  | Int.ofNat n, q => nsmul n q
  | Int.negSucc n, q => -(nsmul (Nat.succ n) q)

instance : AddSemigroup Cl11 := by
  refine AddSemigroup.mk ?_
  intro a b c
  change add (add a b) c = add a (add b c)
  ext <;> simp [add] <;> ring

instance : AddMonoid Cl11 := by
  refine AddMonoid.mk ?_ ?_ nsmul
  · intro a
    change add zero a = a
    ext <;> simp [add, zero]
  · intro a
    change add a zero = a
    ext <;> simp [add, zero]

instance : SubNegMonoid Cl11 := by
  refine SubNegMonoid.mk ?_ zsmul
  intro a b
  change sub a b = add a (neg b)
  ext <;> simp [sub, add, neg] <;> ring

instance : AddGroup Cl11 := by
  refine AddGroup.mk ?_
  intro q
  change add (neg q) q = zero
  ext <;> simp [zero, add, neg]

instance : Mul Cl11 where
  mul := mul

/-- Positive generator `e₁`. -/
def e1Basis : Cl11 :=
  ⟨0, 1, 0, 0⟩

/-- Negative generator `e₂`. -/
def e2Basis : Cl11 :=
  ⟨0, 0, 1, 0⟩

/-- Bivector generator `e₁₂`. -/
def e12Basis : Cl11 :=
  ⟨0, 0, 0, 1⟩

/-- `e₁² = 1`. -/
theorem e1_sq :
    e1Basis * e1Basis = 1 := by
  change mul e1Basis e1Basis = one
  ext <;> norm_num [mul, e1Basis, one]

/-- `e₂² = -1`. -/
theorem e2_sq :
    e2Basis * e2Basis = -1 := by
  change mul e2Basis e2Basis = neg one
  ext <;> norm_num [mul, e2Basis, one, neg]

/-- The bivector convention is `e₁₂ = e₁ * e₂`. -/
theorem e12_eq_e1_mul_e2 :
    e1Basis * e2Basis = e12Basis := by
  change mul e1Basis e2Basis = e12Basis
  ext <;> norm_num [mul, e1Basis, e2Basis, e12Basis]

/-- The generators anticommute: `e₂ * e₁ = -e₁₂`. -/
theorem e2_mul_e1 :
    e2Basis * e1Basis = -e12Basis := by
  change mul e2Basis e1Basis = neg e12Basis
  ext <;> norm_num [mul, e1Basis, e2Basis, e12Basis, neg]

/-- `e₁₂² = 1`. -/
theorem e12_sq :
    e12Basis * e12Basis = 1 := by
  change mul e12Basis e12Basis = one
  ext <;> norm_num [mul, e12Basis, one]

/-- The coordinate product is associative. -/
theorem mul_assoc (q₁ q₂ q₃ : Cl11) :
    (q₁ * q₂) * q₃ = q₁ * (q₂ * q₃) := by
  change mul (mul q₁ q₂) q₃ = mul q₁ (mul q₂ q₃)
  ext <;> simp [mul] <;> ring

/-- The coordinate `1` is a left identity. -/
theorem one_mul (q : Cl11) :
    1 * q = q := by
  change mul one q = q
  ext <;> simp [one, mul]

/-- The coordinate `1` is a right identity. -/
theorem mul_one (q : Cl11) :
    q * 1 = q := by
  change mul q one = q
  ext <;> simp [one, mul]

/-- Left distributivity of the coordinate product. -/
theorem mul_add (a b c : Cl11) :
    a * (b + c) = a * b + a * c := by
  change mul a (add b c) = add (mul a b) (mul a c)
  ext <;> simp [add, mul] <;> ring

/-- Right distributivity of the coordinate product. -/
theorem add_mul (a b c : Cl11) :
    (a + b) * c = a * c + b * c := by
  change mul (add a b) c = add (mul a c) (mul b c)
  ext <;> simp [add, mul] <;> ring

/-- Inner commutator on the finite coordinate algebra. -/
def innerCommutator (K X : Cl11) : Cl11 :=
  K * X - X * K

/-- The finite inner commutator is a derivation of the coordinate product. -/
theorem innerCommutator_isDerivation (K X Y : Cl11) :
    innerCommutator K (X * Y) = innerCommutator K X * Y + X * innerCommutator K Y := by
  unfold innerCommutator
  change sub (mul K (mul X Y)) (mul (mul X Y) K) =
    add (mul (sub (mul K X) (mul X K)) Y) (mul X (sub (mul K Y) (mul Y K)))
  ext <;> simp [mul, sub, add] <;> ring

/-- Inner commutator is additive in the observed coordinate. -/
theorem innerCommutator_add_right (K X Y : Cl11) :
    innerCommutator K (X + Y) = innerCommutator K X + innerCommutator K Y := by
  unfold innerCommutator
  change sub (mul K (add X Y)) (mul (add X Y) K) =
    add (sub (mul K X) (mul X K)) (sub (mul K Y) (mul Y K))
  ext <;> simp [mul, sub, add] <;> ring

/-- Inner commutator is additive in the generator coordinate. -/
theorem innerCommutator_add_left (K₁ K₂ X : Cl11) :
    innerCommutator (K₁ + K₂) X = innerCommutator K₁ X + innerCommutator K₂ X := by
  unfold innerCommutator
  change sub (mul (add K₁ K₂) X) (mul X (add K₁ K₂)) =
    add (sub (mul K₁ X) (mul X K₁)) (sub (mul K₂ X) (mul X K₂))
  ext <;> simp [mul, sub, add] <;> ring

/-- Difference of finite generators gives the difference of their inner commutators. -/
theorem innerCommutator_sub_left (K₁ K₂ X : Cl11) :
    innerCommutator (K₁ - K₂) X = innerCommutator K₁ X - innerCommutator K₂ X := by
  unfold innerCommutator
  change sub (mul (sub K₁ K₂) X) (mul X (sub K₁ K₂)) =
    sub (sub (mul K₁ X) (mul X K₁)) (sub (mul K₂ X) (mul X K₂))
  ext <;> simp [mul, sub] <;> ring

/-- The Clifford reversion on the coordinate algebra. -/
def reverse (q : Cl11) : Cl11 :=
  ⟨q.s, q.e1, q.e2, -q.e12⟩

/-- Grade involution, negating the odd coordinate directions. -/
def gradeInvolution (q : Cl11) : Cl11 :=
  ⟨q.s, -q.e1, -q.e2, q.e12⟩

/-- Clifford conjugation: grade involution followed by reversion. -/
def cliffordConjugate (q : Cl11) : Cl11 :=
  ⟨q.s, -q.e1, -q.e2, -q.e12⟩

/-- The scalar embedding of the real coefficient line. -/
def scalarEmbed (a : ℝ) : Cl11 := ⟨a, 0, 0, 0⟩

@[simp] theorem cliffordConjugate_apply (q : Cl11) :
    cliffordConjugate q = ⟨q.s, -q.e1, -q.e2, -q.e12⟩ := rfl

@[simp] theorem cliffordConjugate_involutive (q : Cl11) :
    cliffordConjugate (cliffordConjugate q) = q := by
  ext <;> simp [cliffordConjugate]

/-- The split quadratic norm of the coordinate `Cl(1,1)` carrier. -/
def splitNorm (q : Cl11) : ℝ :=
  q.s ^ 2 - q.e1 ^ 2 + q.e2 ^ 2 - q.e12 ^ 2

theorem mul_cliffordConjugate (q : Cl11) :
    q * cliffordConjugate q = scalarEmbed (splitNorm q) := by
  change mul q (cliffordConjugate q) = scalarEmbed (splitNorm q)
  ext <;> simp [mul, cliffordConjugate, scalarEmbed, splitNorm] <;> ring

@[simp] theorem splitNorm_cliffordConjugate (q : Cl11) :
    splitNorm (cliffordConjugate q) = splitNorm q := by
  simp [splitNorm, cliffordConjugate]

/-- Krein metric readout in coordinates. -/
def kreinMetric (X Y : Cl11) : ℝ :=
  X.s * Y.s - X.e1 * Y.e1 + X.e2 * Y.e2 - X.e12 * Y.e12

/-- The Krein metric is symmetric. -/
theorem kreinMetric_symm (X Y : Cl11) :
    kreinMetric X Y = kreinMetric Y X := by
  unfold kreinMetric
  ring

/-- The commutator with itself is zero. -/
theorem innerCommutator_self_zero (X : Cl11) :
    innerCommutator X X = 0 := by
  unfold innerCommutator
  exact sub_eq_zero.mpr rfl

/-- Repo-facing alias for the inner commutator. -/
def cl11_commutator (K X : Cl11) : Cl11 :=
  innerCommutator K X

/-- Repo-facing alias for commutator derivation. -/
theorem cl11_commutator_is_derivation (K X Y : Cl11) :
    cl11_commutator K (X * Y) = cl11_commutator K X * Y + X * cl11_commutator K Y := by
  simpa [cl11_commutator] using innerCommutator_isDerivation K X Y

/-- Repo-facing alias for infinitesimal Radon--Nikodym additivity. -/
theorem radon_nikodym_infinitesimal_additivity (K₁ K₂ X : Cl11) :
    cl11_commutator (K₁ - K₂) X = cl11_commutator K₁ X - cl11_commutator K₂ X := by
  simpa [cl11_commutator] using innerCommutator_sub_left K₁ K₂ X

/-!
Closed finite facts in this file:

* the coordinate multiplication table for `Cl(1,1)`;
* associativity and unit readbacks;
* left/right distributivity;
* finite inner-commutator derivation;
* additivity and subtraction of finite inner generators.

Open closure debt, deliberately not encoded as declarations:

* identification of this coordinate commutator with an analytic
  Connes--Radon--Nikodym derivative;
* any von Neumann algebra, spectral triple, or completed modular-flow theorem.
-/

end InfoGeometry.Clifford.Cl11CoordinateAlgebra

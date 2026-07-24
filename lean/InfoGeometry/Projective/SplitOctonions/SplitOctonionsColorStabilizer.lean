import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.SplitOctonionsColorStabilizer

Concrete color-stabilizer action on a `2 × 2` quaternion-block split-octonion
slice.

This file formalizes a block action where the longitudinal block is fixed and
the transverse block is rotated by a unit-norm quaternion.

No wrappers. No `sorry`.
-/

open Quaternion

namespace InfoGeometry.Projective.SplitOctonions.SplitOctonionsColorStabilizer

variable {R : Type*} [CommRing R]

/--
The Bektaş-style `2 × 2` quaternion block slice:

* `q1` = longitudinal/diagonal component
* `q2` = transverse/off-diagonal component
-/
structure BektasMatrix (R : Type*) [CommRing R] where
  q1 : Quaternion R
  q2 : Quaternion R

namespace BektasMatrix

@[ext] theorem ext
    (X Y : BektasMatrix R)
    (h1 : X.q1 = Y.q1)
    (h2 : X.q2 = Y.q2) :
    X = Y := by
  cases X
  cases Y
  simp_all

/--
A color-stabilizer element is represented by a unit-norm quaternion multiplier.
-/
structure ColorStabilizerElement (R : Type*) [CommRing R] where
  u : Quaternion R
  u_unitary : normSq u = 1

/--
Color action:

* keeps the longitudinal block fixed;
* rotates the transverse block by left multiplication with `u`.
-/
def colorAct (g : ColorStabilizerElement R) (X : BektasMatrix R) : BektasMatrix R :=
  { q1 := X.q1
    q2 := g.u * X.q2 }

/--
Multiplicativity of quaternion `normSq`.
-/
theorem normSq_mul (p q : Quaternion R) :
    normSq (p * q) = normSq p * normSq q := by
  have hquat : ((normSq (p * q) : R) : Quaternion R) = (normSq p * normSq q : R) := by
    calc
      ((normSq (p * q) : R) : Quaternion R)
          = (p * q) * star (p * q) := by
              exact (self_mul_star (a := p * q)).symm
      _ = p * (q * star q) * star p := by
            simp [mul_assoc, star_mul]
      _ = p * ((normSq q : R) : Quaternion R) * star p := by
            rw [self_mul_star (a := q)]
      _ = (((normSq q : R) : Quaternion R) * p) * star p := by
            rw [Quaternion.coe_commutes (normSq q) p]
      _ = ((normSq q : R) : Quaternion R) * (p * star p) := by
            simp [mul_assoc]
      _ = ((normSq q : R) : Quaternion R) * ((normSq p : R) : Quaternion R) := by
            rw [self_mul_star (a := p)]
      _ = (normSq q * normSq p : R) := by
            simp [Quaternion.coe_mul]
      _ = (normSq p * normSq q : R) := by ring_nf
  have hre := congrArg (fun z : Quaternion R => z.re) hquat
  simpa using hre

/-- Longitudinal block invariance under the color action. -/
theorem longitudinal_invariant (g : ColorStabilizerElement R) (X : BektasMatrix R) :
    (colorAct g X).q1 = X.q1 := by
  rfl

/-- Transverse norm is preserved by the unitary color action. -/
theorem transverse_norm_preserved (g : ColorStabilizerElement R) (X : BektasMatrix R) :
    normSq (colorAct g X).q2 = normSq X.q2 := by
  dsimp [colorAct]
  rw [normSq_mul, g.u_unitary, one_mul]

/--
Zorn-style split norm on this quaternion block slice:

`normSq q1 - normSq q2`.
-/
def splitNorm (X : BektasMatrix R) : R :=
  normSq X.q1 - normSq X.q2

/-- The split norm is invariant under the color-stabilizer action. -/
theorem splitNorm_invariant (g : ColorStabilizerElement R) (X : BektasMatrix R) :
    splitNorm (colorAct g X) = splitNorm X := by
  unfold splitNorm
  rw [longitudinal_invariant, transverse_norm_preserved]

/-! ## Quaternion-block commutator layer -/

/-- Zero block. -/
def zero : BektasMatrix R :=
  { q1 := 0, q2 := 0 }

/-- Block addition. -/
def add (X Y : BektasMatrix R) : BektasMatrix R :=
  { q1 := X.q1 + Y.q1
    q2 := X.q2 + Y.q2 }

/-- Block negation. -/
def neg (X : BektasMatrix R) : BektasMatrix R :=
  { q1 := -X.q1
    q2 := -X.q2 }

/-- Block subtraction. -/
def sub (X Y : BektasMatrix R) : BektasMatrix R :=
  add X (neg Y)

/-- `X - X = 0` for block subtraction. -/
theorem sub_self (X : BektasMatrix R) : sub X X = zero := by
  ext <;> simp [sub, add, neg, zero]

/-- `X - Y = -(Y - X)` for block subtraction. -/
theorem sub_eq_neg_sub (X Y : BektasMatrix R) :
    sub X Y = neg (sub Y X) := by
  ext <;> simp [sub, add, neg, add_assoc, add_left_comm, add_comm]

/--
Closed multiplication of Bektaş-form `2 × 2` quaternion blocks

`[[q1,q2],[star q2, star q1]] * [[r1,r2],[star r2, star r1]]`.
-/
def blockMul (X Y : BektasMatrix R) : BektasMatrix R :=
  { q1 := X.q1 * Y.q1 + X.q2 * star Y.q2
    q2 := X.q1 * Y.q2 + X.q2 * star Y.q1 }

/-- Quaternion-block commutator `[X,Y] = XY - YX`. -/
def blockComm (X Y : BektasMatrix R) : BektasMatrix R :=
  sub (blockMul X Y) (blockMul Y X)

/-- Component formulas for block multiplication. -/
@[simp] theorem blockMul_q1 (X Y : BektasMatrix R) :
    (blockMul X Y).q1 = X.q1 * Y.q1 + X.q2 * star Y.q2 := rfl

@[simp] theorem blockMul_q2 (X Y : BektasMatrix R) :
    (blockMul X Y).q2 = X.q1 * Y.q2 + X.q2 * star Y.q1 := rfl

/-- Self commutator vanishes. -/
theorem blockComm_self (X : BektasMatrix R) :
    blockComm X X = zero := by
  unfold blockComm
  exact sub_self (blockMul X X)

/-- Antisymmetry of the quaternion-block commutator. -/
theorem blockComm_antisymm (X Y : BektasMatrix R) :
    blockComm X Y = neg (blockComm Y X) := by
  unfold blockComm
  exact sub_eq_neg_sub (blockMul X Y) (blockMul Y X)

/-- Equivalent additive cancellation form of antisymmetry. -/
theorem blockComm_add_swap_eq_zero (X Y : BektasMatrix R) :
    add (blockComm X Y) (blockComm Y X) = zero := by
  rw [blockComm_antisymm]
  ext <;> simp [add, neg, zero]

end BektasMatrix

end InfoGeometry.Projective.SplitOctonions.SplitOctonionsColorStabilizer

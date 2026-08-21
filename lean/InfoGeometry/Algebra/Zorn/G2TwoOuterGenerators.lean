import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

def g2Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b ^^ X.x2 ^^ X.y0,
    X.a ^^ X.x2 ^^ X.y0,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2,
    X.x2 ^^ X.y1,
    X.y0,
    X.x2,
    X.x1 ^^ X.y0,
    X.a ^^ X.b ^^ X.x0 ^^ X.x2 ^^ X.y0 ^^ X.y1⟩

def g4Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x2,
    X.b ^^ X.x2,
    X.x0 ^^ X.y1,
    X.x1 ^^ X.y0,
    X.x2,
    X.y0,
    X.y1,
    X.a ^^ X.b ^^ X.x2 ^^ X.y2⟩

theorem g2Fun_add (X Y : SplitOctF2) :
    g2Fun (add X Y) = add (g2Fun X) (g2Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g2Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g4Fun_add (X Y : SplitOctF2) :
    g4Fun (add X Y) = add (g4Fun X) (g4Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g4Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g2Fun_one : g2Fun one = one := by
  dsimp [g2Fun, one]
  rfl

theorem g4Fun_one : g4Fun one = one := by
  dsimp [g4Fun, one]
  rfl

theorem g2Fun_involutive (X : SplitOctF2) : g2Fun (g2Fun X) = X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [g2Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g4Fun_involutive (X : SplitOctF2) : g4Fun (g4Fun X) = X := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  ext <;> dsimp [g4Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

lemma F2_mul_two (x : F2) : x * 2 = 0 := by
  fin_cases x <;> rfl

lemma F2_mul_three (x : F2) : x * 3 = x := by
  fin_cases x <;> rfl

lemma F2_mul_four (x : F2) : x * 4 = 0 := by
  fin_cases x <;> rfl

theorem g2Fun_mul (X Y : SplitOctF2) :
    g2Fun (mul X Y) = mul (g2Fun X) (g2Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [g2Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf
    simp only [F2_mul_two, F2_mul_three, F2_mul_four]
    ring

theorem g4Fun_mul (X Y : SplitOctF2) :
    g4Fun (mul X Y) = mul (g4Fun X) (g4Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [g4Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf
    simp only [F2_mul_two]
    ring

def g2Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := g2Fun
  invFun := g2Fun
  left_inv := g2Fun_involutive
  right_inv := g2Fun_involutive

def g4Equiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := g4Fun
  invFun := g4Fun
  left_inv := g4Fun_involutive
  right_inv := g4Fun_involutive

def g2Aut : SplitOctF2Aut :=
  ⟨g2Equiv, g2Fun_one, g2Fun_add, g2Fun_mul⟩

def g4Aut : SplitOctF2Aut :=
  ⟨g4Equiv, g4Fun_one, g4Fun_add, g4Fun_mul⟩

theorem g2Aut_sq : g2Aut * g2Aut = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  exact g2Fun_involutive

theorem g4Aut_sq : g4Aut * g4Aut = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  exact g4Fun_involutive

end InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators

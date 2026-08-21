import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import Mathlib.Algebra.Ring.BooleanRing

namespace InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

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

private theorem bool_and_eq_mul (a b : Bool) : a && b = a * b := rfl

private theorem bool_xor_eq_add (a b : Bool) : a ^^ b = a + b := rfl

theorem g2Fun_mul (X Y : SplitOctF2) :
    g2Fun (mul X Y) = mul (g2Fun X) (g2Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g2Fun, mul, add2, mul2, dot3, cross0, cross1, cross2]
  all_goals simp only [bool_and_eq_mul, bool_xor_eq_add]
  all_goals ring

theorem g4Fun_mul (X Y : SplitOctF2) :
    g4Fun (mul X Y) = mul (g4Fun X) (g4Fun Y) := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨a', b', x0', x1', x2', y0', y1', y2'⟩
  ext <;> dsimp [g4Fun, mul, add2, mul2, dot3, cross0, cross1, cross2]
  all_goals simp only [bool_and_eq_mul, bool_xor_eq_add]
  all_goals ring

end InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators

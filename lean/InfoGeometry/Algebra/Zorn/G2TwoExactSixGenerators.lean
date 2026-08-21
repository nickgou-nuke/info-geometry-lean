import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2TwoExactSixGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

lemma F2_mul_two (x : F2) : x * 2 = 0 := by fin_cases x <;> rfl
lemma F2_mul_three (x : F2) : x * 3 = x := by fin_cases x <;> rfl
lemma F2_mul_four (x : F2) : x * 4 = 0 := by fin_cases x <;> rfl

/- The six matrices exported by the carrier-level CAS artifact, written as
   coordinate maps.  The coordinate order is (a,b,x0,x1,x2,y0,y1,y2). -/
def g1 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b, X.a, X.y2, X.y1, X.y0, X.x2, X.x1, X.x0⟩

def g2 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b, X.a, X.y1 ^^ X.y2, X.y0 ^^ X.y1, X.y0, X.x2,
    X.x1 ^^ X.x2, X.x0 ^^ X.x1 ^^ X.x2⟩

def g3 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b ^^ X.x2 ^^ X.y0, X.a ^^ X.x2 ^^ X.y0,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2, X.x2 ^^ X.y1,
    X.y0, X.x2, X.x1 ^^ X.y0, X.a ^^ X.b ^^ X.x0 ^^ X.x2 ^^ X.y0 ^^ X.y1⟩

def g4 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0, X.x1 ^^ X.x2, X.x2, X.y0, X.y1, X.y1 ^^ X.y2⟩

def g5 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x2, X.b ^^ X.x2, X.x0 ^^ X.y1, X.x1 ^^ X.y0,
    X.x2, X.y0, X.y1, X.a ^^ X.b ^^ X.x2 ^^ X.y2⟩

def g6 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b, X.a, X.y1, X.y0, X.y2, X.x1, X.x0, X.x2⟩

theorem g1_add (X Y : SplitOctF2) : g1 (add X Y) = add (g1 X) (g1 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [g1, add, add2]

theorem g2_add (X Y : SplitOctF2) : g2 (add X Y) = add (g2 X) (g2 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [g2, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g3_add (X Y : SplitOctF2) : g3 (add X Y) = add (g3 X) (g3 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [g3, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g4_add (X Y : SplitOctF2) : g4 (add X Y) = add (g4 X) (g4 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [g4, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g5_add (X Y : SplitOctF2) : g5 (add X Y) = add (g5 X) (g5 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [g5, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g6_add (X Y : SplitOctF2) : g6 (add X Y) = add (g6 X) (g6 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [g6, add, add2]

theorem g1_involutive (X : SplitOctF2) : g1 (g1 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rfl

theorem g2_involutive (X : SplitOctF2) : g2 (g2 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [g2, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g3_involutive (X : SplitOctF2) : g3 (g3 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [g3, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g4_involutive (X : SplitOctF2) : g4 (g4 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [g4, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g5_involutive (X : SplitOctF2) : g5 (g5 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [g5, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem g6_involutive (X : SplitOctF2) : g6 (g6 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rfl

theorem g1_mul (X Y : SplitOctF2) : g1 (mul X Y) = mul (g1 X) (g1 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [g1, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf 

theorem g2_mul (X Y : SplitOctF2) : g2 (mul X Y) = mul (g2 X) (g2 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [g2, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp only [F2_mul_two] <;>
    ring

theorem g3_mul (X Y : SplitOctF2) : g3 (mul X Y) = mul (g3 X) (g3 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [g3, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp only [F2_mul_two, F2_mul_three, F2_mul_four] <;>
    ring

theorem g4_mul (X Y : SplitOctF2) : g4 (mul X Y) = mul (g4 X) (g4 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [g4, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp only [F2_mul_two] <;>
    ring

theorem g5_mul (X Y : SplitOctF2) : g5 (mul X Y) = mul (g5 X) (g5 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [g5, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp only [F2_mul_two] <;>
    ring

theorem g6_mul (X Y : SplitOctF2) : g6 (mul X Y) = mul (g6 X) (g6 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [g6, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf 

end InfoGeometry.Algebra.Zorn.G2TwoExactSixGenerators

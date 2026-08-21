import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import Mathlib.Tactic

set_option maxHeartbeats 1000000

namespace InfoGeometry.Algebra.Zorn.G2TwoPCGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

lemma F2_mul_two (x : F2) : x * 2 = 0 := by
  fin_cases x <;> rfl

lemma F2_mul_three (x : F2) : x * 3 = x := by
  fin_cases x <;> rfl

lemma F2_mul_four (x : F2) : x * 4 = 0 := by
  fin_cases x <;> rfl

lemma F2_bit_sq (x : Bool) :
    bitToF2 x * bitToF2 x = bitToF2 x := by
  cases x <;> simp [bitToF2]

def pc1Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x1, X.b ^^ X.x1, X.x0 ^^ X.y2, X.x1,
    X.x1 ^^ X.x2 ^^ X.y0, X.y0,
    X.a ^^ X.b ^^ X.x1 ^^ X.y0 ^^ X.y1 ^^ X.y2, X.y2⟩

def pc2Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.y2, X.b ^^ X.y2, X.x0, X.x0 ^^ X.x1,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2,
    X.x0 ^^ X.x1 ^^ X.y0 ^^ X.y1 ^^ X.y2,
    X.x0 ^^ X.y0 ^^ X.y2, X.y2⟩

def pc3Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x0 ^^ X.y2, X.b ^^ X.x0 ^^ X.y2, X.x0, X.x1 ^^ X.y2,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y0,
    X.a ^^ X.b ^^ X.x0 ^^ X.x1 ^^ X.y0 ^^ X.y1 ^^ X.y2,
    X.x0 ^^ X.y1 ^^ X.y2, X.y2⟩

def pc4Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0, X.x1 ^^ X.x2, X.x2, X.y0, X.y1, X.y1 ^^ X.y2⟩

def pc5Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.y2, X.b ^^ X.y2, X.x0, X.x1,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2, X.x1 ^^ X.y0,
    X.x0 ^^ X.y1 ^^ X.y2, X.y2⟩

def pc6Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0 ^^ X.x2, X.x1, X.x2, X.y0, X.y1, X.y1 ^^ X.y2⟩

theorem pc1Fun_add (X Y : SplitOctF2) : pc1Fun (add X Y) = add (pc1Fun X) (pc1Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩; rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc1Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc2Fun_add (X Y : SplitOctF2) : pc2Fun (add X Y) = add (pc2Fun X) (pc2Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩; rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc2Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc3Fun_add (X Y : SplitOctF2) : pc3Fun (add X Y) = add (pc3Fun X) (pc3Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩; rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc3Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc4Fun_add (X Y : SplitOctF2) : pc4Fun (add X Y) = add (pc4Fun X) (pc4Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩; rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc4Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc5Fun_add (X Y : SplitOctF2) : pc5Fun (add X Y) = add (pc5Fun X) (pc5Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩; rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc5Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc6Fun_add (X Y : SplitOctF2) : pc6Fun (add X Y) = add (pc6Fun X) (pc6Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩; rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [pc6Fun, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem pc1Fun_one : pc1Fun one = one := by rfl
theorem pc2Fun_one : pc2Fun one = one := by rfl
theorem pc3Fun_one : pc3Fun one = one := by rfl
theorem pc4Fun_one : pc4Fun one = one := by rfl
theorem pc5Fun_one : pc5Fun one = one := by rfl
theorem pc6Fun_one : pc6Fun one = one := by rfl

theorem pc1Fun_mul (X Y : SplitOctF2) :
    pc1Fun (mul X Y) = mul (pc1Fun X) (pc1Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [pc1Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf <;> simp [F2_mul_two, F2_mul_three, F2_mul_four, F2_bit_sq]

theorem pc2Fun_mul (X Y : SplitOctF2) :
    pc2Fun (mul X Y) = mul (pc2Fun X) (pc2Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [pc2Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf <;> simp [F2_mul_two, F2_mul_three, F2_mul_four, F2_bit_sq]

theorem pc3Fun_mul (X Y : SplitOctF2) :
    pc3Fun (mul X Y) = mul (pc3Fun X) (pc3Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [pc3Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf <;> simp [F2_mul_two, F2_mul_three, F2_mul_four, F2_bit_sq]

theorem pc4Fun_mul (X Y : SplitOctF2) :
    pc4Fun (mul X Y) = mul (pc4Fun X) (pc4Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [pc4Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf <;> simp [F2_mul_two, F2_mul_three, F2_mul_four, F2_bit_sq]

theorem pc5Fun_mul (X Y : SplitOctF2) :
    pc5Fun (mul X Y) = mul (pc5Fun X) (pc5Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [pc5Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf <;> simp [F2_mul_two, F2_mul_three, F2_mul_four, F2_bit_sq]

theorem pc6Fun_mul (X Y : SplitOctF2) :
    pc6Fun (mul X Y) = mul (pc6Fun X) (pc6Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff]
  all_goals
    simp only [pc6Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and]
    ring_nf <;> simp [F2_mul_two, F2_mul_three, F2_mul_four, F2_bit_sq]

theorem pc1Fun_involutive (X : SplitOctF2) : pc1Fun (pc1Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [pc1Fun, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc4Fun_involutive (X : SplitOctF2) : pc4Fun (pc4Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [pc4Fun, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc5Fun_involutive (X : SplitOctF2) : pc5Fun (pc5Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [pc5Fun, add2, Bool.xor_left_comm, Bool.xor_comm]
theorem pc6Fun_involutive (X : SplitOctF2) : pc6Fun (pc6Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [pc6Fun, add2, Bool.xor_left_comm, Bool.xor_comm]

end InfoGeometry.Algebra.Zorn.G2TwoPCGenerators

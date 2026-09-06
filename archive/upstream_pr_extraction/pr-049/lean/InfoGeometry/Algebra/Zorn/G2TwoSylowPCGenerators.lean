import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer

lemma F2_mul_two (x : F2) : x * 2 = 0 := by fin_cases x <;> rfl
lemma F2_mul_three (x : F2) : x * 3 = x := by fin_cases x <;> rfl
lemma F2_mul_four (x : F2) : x * 4 = 0 := by fin_cases x <;> rfl

def pc1Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x1, X.b ^^ X.x1, X.x0 ^^ X.y2, X.x1,
    X.x1 ^^ X.x2 ^^ X.y0, X.y0,
    X.a ^^ X.b ^^ X.x1 ^^ X.y1 ^^ X.y2, X.y2⟩

def pc2Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.y2, X.b ^^ X.y2, X.x0, X.x0 ^^ X.x1,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2,
    X.x0 ^^ X.x1 ^^ X.y0 ^^ X.y1 ^^ X.y2,
    X.x0 ^^ X.y1 ^^ X.y2, X.y2⟩

def pc3Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x0 ^^ X.y2, X.b ^^ X.x0 ^^ X.y2, X.x0, X.x1 ^^ X.y2,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y1,
    X.a ^^ X.b ^^ X.x0 ^^ X.x1 ^^ X.y0 ^^ X.y2,
    X.x0 ^^ X.y1 ^^ X.y2, X.y2⟩

def pc4Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0, X.x1, X.x1 ^^ X.x2, X.y0,
    X.y1 ^^ X.y2, X.y2⟩

def pc5Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.y2, X.b ^^ X.y2, X.x0, X.x1,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2, X.x1 ^^ X.y0,
    X.x0 ^^ X.y1 ^^ X.y2, X.y2⟩

def pc6Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0, X.x1, X.x0 ^^ X.x2, X.y0 ^^ X.y2,
    X.y1, X.y2⟩

theorem pc1_mul (X Y : SplitOctF2) :
    pc1Fun (mul X Y) = mul (pc1Fun X) (pc1Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc1Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp [F2_mul_two]

theorem pc2_mul (X Y : SplitOctF2) :
    pc2Fun (mul X Y) = mul (pc2Fun X) (pc2Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc2Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp [F2_mul_two, F2_mul_four]

theorem pc3_mul (X Y : SplitOctF2) :
    pc3Fun (mul X Y) = mul (pc3Fun X) (pc3Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc3Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp [F2_mul_two, F2_mul_three, F2_mul_four]

theorem pc4_mul (X Y : SplitOctF2) :
    pc4Fun (mul X Y) = mul (pc4Fun X) (pc4Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc4Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp [F2_mul_two]

theorem pc5_mul (X Y : SplitOctF2) :
    pc5Fun (mul X Y) = mul (pc5Fun X) (pc5Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc5Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp [F2_mul_two]

theorem pc6_mul (X Y : SplitOctF2) :
    pc6Fun (mul X Y) = mul (pc6Fun X) (pc6Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> rw [← bitToF2_eq_iff] <;>
    simp only [pc6Fun, mul, add2, mul2, dot3, cross0, cross1, cross2,
      bitToF2_xor, bitToF2_and] <;>
    ring_nf <;>
    simp [F2_mul_two]

theorem pc1_sq (X : SplitOctF2) : pc1Fun (pc1Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc1Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc4_sq (X : SplitOctF2) : pc4Fun (pc4Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc4Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc5_sq (X : SplitOctF2) : pc5Fun (pc5Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc5Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc6_sq (X : SplitOctF2) : pc6Fun (pc6Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc6Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc2_sq (X : SplitOctF2) :
    pc2Fun (pc2Fun X) = pc6Fun X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc2Fun, pc6Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc3_sq (X : SplitOctF2) :
    pc3Fun (pc3Fun X) = pc6Fun X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc3Fun, pc6Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc1_add (X Y : SplitOctF2) :
    pc1Fun (add X Y) = add (pc1Fun X) (pc1Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc1Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc2_add (X Y : SplitOctF2) :
    pc2Fun (add X Y) = add (pc2Fun X) (pc2Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc2Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc3_add (X Y : SplitOctF2) :
    pc3Fun (add X Y) = add (pc3Fun X) (pc3Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc3Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc4_add (X Y : SplitOctF2) :
    pc4Fun (add X Y) = add (pc4Fun X) (pc4Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc4Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc5_add (X Y : SplitOctF2) :
    pc5Fun (add X Y) = add (pc5Fun X) (pc5Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc5Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc6_add (X Y : SplitOctF2) :
    pc6Fun (add X Y) = add (pc6Fun X) (pc6Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc6Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc1_one : pc1Fun one = one := by rfl
theorem pc2_one : pc2Fun one = one := by rfl
theorem pc3_one : pc3Fun one = one := by rfl
theorem pc4_one : pc4Fun one = one := by rfl
theorem pc5_one : pc5Fun one = one := by rfl
theorem pc6_one : pc6Fun one = one := by rfl

theorem pc1_injective : Function.Injective pc1Fun := by
  intro X Y h
  rw [← pc1_sq X, ← pc1_sq Y, h]
theorem pc4_injective : Function.Injective pc4Fun := by
  intro X Y h
  rw [← pc4_sq X, ← pc4_sq Y, h]
theorem pc5_injective : Function.Injective pc5Fun := by
  intro X Y h
  rw [← pc5_sq X, ← pc5_sq Y, h]
theorem pc6_injective : Function.Injective pc6Fun := by
  intro X Y h
  rw [← pc6_sq X, ← pc6_sq Y, h]

theorem pc2_four (X : SplitOctF2) :
    pc2Fun (pc2Fun (pc2Fun (pc2Fun X))) = X := by
  rw [pc2_sq, pc2_sq, pc6_sq]

theorem pc3_four (X : SplitOctF2) :
    pc3Fun (pc3Fun (pc3Fun (pc3Fun X))) = X := by
  rw [pc3_sq, pc3_sq, pc6_sq]

theorem pc2_injective : Function.Injective pc2Fun := by
  intro X Y h
  have h' := congrArg (fun Z => pc2Fun (pc2Fun (pc2Fun Z))) h
  calc
    X = pc2Fun (pc2Fun (pc2Fun (pc2Fun X))) := (pc2_four X).symm
    _ = pc2Fun (pc2Fun (pc2Fun (pc2Fun Y))) := h'
    _ = Y := pc2_four Y

theorem pc3_injective : Function.Injective pc3Fun := by
  intro X Y h
  have h' := congrArg (fun Z => pc3Fun (pc3Fun (pc3Fun Z))) h
  calc
    X = pc3Fun (pc3Fun (pc3Fun (pc3Fun X))) := (pc3_four X).symm
    _ = pc3Fun (pc3Fun (pc3Fun (pc3Fun Y))) := h'
    _ = Y := pc3_four Y

noncomputable def pc1Equiv : SplitOctF2 ≃ SplitOctF2 :=
  Equiv.ofBijective pc1Fun ⟨pc1_injective, by
    intro X
    exact ⟨pc1Fun X, pc1_sq X⟩⟩

noncomputable def pc4Equiv : SplitOctF2 ≃ SplitOctF2 :=
  Equiv.ofBijective pc4Fun ⟨pc4_injective, by
    intro X
    exact ⟨pc4Fun X, pc4_sq X⟩⟩

noncomputable def pc5Equiv : SplitOctF2 ≃ SplitOctF2 :=
  Equiv.ofBijective pc5Fun ⟨pc5_injective, by
    intro X
    exact ⟨pc5Fun X, pc5_sq X⟩⟩

noncomputable def pc6Equiv : SplitOctF2 ≃ SplitOctF2 :=
  Equiv.ofBijective pc6Fun ⟨pc6_injective, by
    intro X
    exact ⟨pc6Fun X, pc6_sq X⟩⟩

noncomputable def pc2Equiv : SplitOctF2 ≃ SplitOctF2 :=
  Equiv.ofBijective pc2Fun ⟨pc2_injective, by
    intro X
    exact ⟨pc2Fun (pc2Fun (pc2Fun X)), pc2_four X⟩⟩

noncomputable def pc3Equiv : SplitOctF2 ≃ SplitOctF2 :=
  Equiv.ofBijective pc3Fun ⟨pc3_injective, by
    intro X
    exact ⟨pc3Fun (pc3Fun (pc3Fun X)), pc3_four X⟩⟩

noncomputable def pc1Aut : SplitOctF2Aut := ⟨pc1Equiv, pc1_one, pc1_add, pc1_mul⟩
noncomputable def pc4Aut : SplitOctF2Aut := ⟨pc4Equiv, pc4_one, pc4_add, pc4_mul⟩
noncomputable def pc5Aut : SplitOctF2Aut := ⟨pc5Equiv, pc5_one, pc5_add, pc5_mul⟩
noncomputable def pc6Aut : SplitOctF2Aut := ⟨pc6Equiv, pc6_one, pc6_add, pc6_mul⟩
noncomputable def pc2Aut : SplitOctF2Aut := ⟨pc2Equiv, pc2_one, pc2_add, pc2_mul⟩
noncomputable def pc3Aut : SplitOctF2Aut := ⟨pc3Equiv, pc3_one, pc3_add, pc3_mul⟩

end InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators

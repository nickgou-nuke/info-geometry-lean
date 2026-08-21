import InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators

namespace InfoGeometry.Algebra.Zorn.G2TwoPCGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators

/-! The PC-normal-form generators exported from GAP.  Their order is the
    polycyclic order, not the original CAS matrix order. -/

def pc1Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0 ^^ X.x1, X.x1, X.x2, X.y0, X.y0 ^^ X.y1, X.y2⟩

def pc3Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b ^^ X.y0, X.a ^^ X.y0, X.x1 ^^ X.y2,
    X.x2 ^^ X.y0 ^^ X.y1, X.y0, X.x1, X.x2,
    X.a ^^ X.b ^^ X.x0 ^^ X.x1 ^^ X.y0⟩

def pc5Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x2 ^^ X.y0, X.b ^^ X.x2 ^^ X.y0,
    X.a ^^ X.b ^^ X.x0 ^^ X.y0 ^^ X.y1, X.x1 ^^ X.x2,
    X.x2, X.y0, X.y0 ^^ X.y1,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y0 ^^ X.y2⟩

def pc6Fun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0 ^^ X.x2, X.x1, X.x2, X.y0, X.y1, X.y0 ^^ X.y2⟩

theorem pc1Fun_add (X Y : SplitOctF2) :
    pc1Fun (add X Y) = add (pc1Fun X) (pc1Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc1Fun, add, add2]
  all_goals simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem pc3Fun_add (X Y : SplitOctF2) :
    pc3Fun (add X Y) = add (pc3Fun X) (pc3Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc3Fun, add, add2]
  all_goals simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem pc5Fun_add (X Y : SplitOctF2) :
    pc5Fun (add X Y) = add (pc5Fun X) (pc5Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc5Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc6Fun_add (X Y : SplitOctF2) :
    pc6Fun (add X Y) = add (pc6Fun X) (pc6Fun Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> dsimp [pc6Fun, add, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc1Fun_one : pc1Fun one = one := by rfl
theorem pc3Fun_one : pc3Fun one = one := by rfl
theorem pc5Fun_one : pc5Fun one = one := by rfl
theorem pc6Fun_one : pc6Fun one = one := by rfl

theorem pc1Fun_involutive (X : SplitOctF2) : pc1Fun (pc1Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc1Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

theorem pc3Fun_involutive (X : SplitOctF2) : pc3Fun (pc3Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc3Fun, add2]
  all_goals simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem pc5Fun_involutive (X : SplitOctF2) : pc5Fun (pc5Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc5Fun, add2]
  all_goals simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem pc6Fun_involutive (X : SplitOctF2) : pc6Fun (pc6Fun X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> dsimp [pc6Fun, add2]
  all_goals simp [Bool.xor_left_comm, Bool.xor_comm]

end InfoGeometry.Algebra.Zorn.G2TwoPCGenerators
